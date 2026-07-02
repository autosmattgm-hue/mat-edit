(function(){
"use strict";

/* ============================================================
   VULL EDITOR — core engine
   Video track drives sequence length. Text + audio overlay it.
   Preview uses scrub-seek compositing; export uses real playback
   through a MediaRecorder + Web Audio mix so clip/track audio
   actually makes it into the file.
   ============================================================ */

const CANVAS_W = 1280, CANVAS_H = 720;
const IMAGE_DEFAULT_DURATION = 4; // seconds, at speed 1

const $ = (sel, root=document) => root.querySelector(sel);
const $$ = (sel, root=document) => Array.from(root.querySelectorAll(sel));
const uid = () => Math.random().toString(36).slice(2,10);

const els = {
  fileInput: $('#fileInput'), dropzone: $('#dropzone'), mediaGrid: $('#mediaGrid'),
  audioInput: $('#audioInput'), audioDropzone: $('#audioDropzone'),
  canvas: $('#previewCanvas'), canvasWrap: $('#canvasWrap'), emptyStage: $('#emptyStage'),
  overlayLayer: $('#overlayLayer'), transport: $('#transport'),
  btnPlay: $('#btnPlay'), iconPlay: $('#iconPlay'),
  tCurrent: $('#tCurrent'), tTotal: $('#tTotal'),
  btnSplit: $('#btnSplit'), btnDeleteClip: $('#btnDeleteClip'),
  tlTracks: $('#tlTracks'), tlRuler: $('#tlRuler'), tlPlayhead: $('#tlPlayhead'), tlBody: $('#tlBody'),
  laneVideo: $('#laneVideo'), laneText: $('#laneText'), laneAudio: $('#laneAudio'),
  rngZoom: $('#rngZoom'),
  layersList: $('#layersList'), layersEmpty: $('#layersEmpty'),
  toast: $('#toast'),
  btnExport: $('#btnExport'), exportModal: $('#exportModal'), btnStartExport: $('#btnStartExport'),
  btnCancelExport: $('#btnCancelExport'), exportSetup: $('#exportSetup'), exportProgress: $('#exportProgress'),
  progressFill: $('#progressFill'), progressLabel: $('#progressLabel'), selRes: $('#selRes'),
  btnInstall: $('#btnInstall'), projName: $('#projName'),
  btnEmptyImport: $('#btnEmptyImport'), btnUndo: $('#btnUndo'), btnRedo: $('#btnRedo'),
};
const ctx = els.canvas.getContext('2d');

/* ---------------- state ---------------- */
const state = {
  clips: [],        // video track
  texts: [],        // text overlays
  music: null,       // {url, el, name, volume}
  playhead: 0,
  playing: false,
  selectedClipId: null,
  selectedTextId: null,
  zoomPxPerSec: 70,
  totalDuration: 0,
};

let rafId = null;
let lastFrameTs = 0;

/* ---------------- helpers ---------------- */
function fmtTime(s){
  if(!isFinite(s) || s < 0) s = 0;
  const m = Math.floor(s/60);
  const sec = Math.floor(s%60);
  const cs = Math.floor((s - Math.floor(s))*100);
  return `${String(m).padStart(2,'0')}:${String(sec).padStart(2,'0')}.${String(cs).padStart(2,'0')}`;
}
function toast(msg){
  els.toast.textContent = msg;
  els.toast.classList.add('show');
  clearTimeout(toast._t);
  toast._t = setTimeout(()=>els.toast.classList.remove('show'), 2200);
}
function clamp(v,a,b){ return Math.max(a, Math.min(b, v)); }

function defaultFilters(){
  return { brightness:100, contrast:100, saturation:100, temp:0, vignette:0 };
}

/* ---------------- timeline math ---------------- */
function clipEffectiveDuration(c){
  const raw = (c.trimOut - c.trimIn);
  return Math.max(0.02, raw / c.speed);
}
function recalcTimeline(){
  let t = 0;
  for(const c of state.clips){
    c.seqStart = t;
    c.seqDur = clipEffectiveDuration(c);
    t += c.seqDur;
  }
  state.totalDuration = t;
  if(state.playhead > t) state.playhead = t;
  els.tTotal.textContent = fmtTime(t);
}
function getActiveClip(time){
  for(const c of state.clips){
    if(time >= c.seqStart && time < c.seqStart + c.seqDur) return c;
  }
  if(state.clips.length && time >= state.totalDuration) return state.clips[state.clips.length-1];
  return null;
}
function localTimeFor(c, seqTime){
  const elapsed = (seqTime - c.seqStart) * c.speed;
  return clamp(c.trimIn + elapsed, c.trimIn, c.trimOut);
}

/* ---------------- media import ---------------- */
function acceptFiles(fileList){
  const files = Array.from(fileList || []);
  files.forEach(file => {
    const isVideo = file.type.startsWith('video/');
    const isImage = file.type.startsWith('image/');
    if(!isVideo && !isImage) return;
    const url = URL.createObjectURL(file);

    if(isVideo){
      const v = document.createElement('video');
      v.src = url; v.muted = false; v.playsInline = true; v.preload = 'auto';
      v.addEventListener('loadedmetadata', () => {
        const clip = {
          id: uid(), kind:'video', name:file.name, url, el:v,
          naturalDuration: v.duration, trimIn:0, trimOut: v.duration,
          speed:1, filters: defaultFilters(), volume:100, muted:false,
          seqStart:0, seqDur:0, thumbReady:false, _audioNode:null,
        };
        state.clips.push(clip);
        addMediaThumb(clip, v);
        finalizeAdd(clip);
      });
      v.addEventListener('error', ()=> toast(`Couldn't load ${file.name}`));
    } else {
      const img = new Image();
      img.onload = () => {
        const clip = {
          id: uid(), kind:'image', name:file.name, url, el:img,
          naturalDuration: IMAGE_DEFAULT_DURATION, trimIn:0, trimOut: IMAGE_DEFAULT_DURATION,
          speed:1, filters: defaultFilters(), volume:0, muted:true,
          seqStart:0, seqDur:0,
        };
        state.clips.push(clip);
        addMediaThumb(clip, img);
        finalizeAdd(clip);
      };
      img.onerror = ()=> toast(`Couldn't load ${file.name}`);
      img.src = url;
    }
  });
}
function finalizeAdd(clip){
  recalcTimeline();
  renderTimeline();
  renderLayers();
  showStage();
  selectClip(clip.id);
  renderFrame();
  toast(`Added ${clip.name}`);
}
function addMediaThumb(clip, mediaEl){
  const item = document.createElement('div');
  item.className = 'media-item';
  item.draggable = false;
  item.title = 'Click to add to timeline';
  const thumb = clip.kind === 'video' ? document.createElement('video') : document.createElement('img');
  thumb.src = clip.url;
  if(clip.kind === 'video'){ thumb.muted = true; thumb.preload='metadata'; }
  const tag = document.createElement('div');
  tag.className = 'tag';
  tag.textContent = clip.kind === 'video' ? fmtTime(clip.naturalDuration).slice(0,5) : 'IMG';
  const badge = document.createElement('div');
  badge.className = 'add-badge';
  badge.textContent = '+';
  item.append(thumb, tag, badge);
  item.addEventListener('click', () => {
    // clone as a new timeline entry (reuse same media el clone for independent playback)
    addExistingToTimeline(clip);
  });
  els.mediaGrid.appendChild(item);
}
function addExistingToTimeline(sourceClip){
  if(state.clips.some(c => c === sourceClip)){
    recalcTimeline(); renderTimeline(); renderLayers(); renderFrame();
    return; // first import already placed it; subsequent clicks duplicate below
  }
}
// Duplicate-from-bin support: create a fresh clip referencing the same URL
function duplicateMediaToTimeline(kind, url, name, naturalDuration){
  if(kind === 'video'){
    const v = document.createElement('video');
    v.src = url; v.preload = 'auto'; v.playsInline = true;
    v.addEventListener('loadedmetadata', () => {
      const clip = { id: uid(), kind:'video', name, url, el:v, naturalDuration:v.duration,
        trimIn:0, trimOut:v.duration, speed:1, filters:defaultFilters(), volume:100, muted:false,
        seqStart:0, seqDur:0, _audioNode:null };
      state.clips.push(clip); recalcTimeline(); renderTimeline(); renderLayers(); renderFrame();
      selectClip(clip.id);
    });
  } else {
    const img = new Image();
    img.onload = () => {
      const clip = { id: uid(), kind:'image', name, url, el:img, naturalDuration:IMAGE_DEFAULT_DURATION,
        trimIn:0, trimOut:IMAGE_DEFAULT_DURATION, speed:1, filters:defaultFilters(), volume:0, muted:true,
        seqStart:0, seqDur:0 };
      state.clips.push(clip); recalcTimeline(); renderTimeline(); renderLayers(); renderFrame();
      selectClip(clip.id);
    };
    img.src = url;
  }
}

els.fileInput.addEventListener('change', e => acceptFiles(e.target.files));
els.dropzone.addEventListener('click', () => els.fileInput.click());
['dragover','dragenter'].forEach(ev => els.dropzone.addEventListener(ev, e=>{ e.preventDefault(); els.dropzone.classList.add('drag'); }));
['dragleave','drop'].forEach(ev => els.dropzone.addEventListener(ev, e=>{ e.preventDefault(); els.dropzone.classList.remove('drag'); }));
els.dropzone.addEventListener('drop', e => acceptFiles(e.dataTransfer.files));
els.btnEmptyImport.addEventListener('click', () => els.fileInput.click());

// Global page-level drag/drop convenience
window.addEventListener('dragover', e=> e.preventDefault());
window.addEventListener('drop', e=>{ e.preventDefault(); });

function showStage(){
  if(state.clips.length){
    els.emptyStage.style.display = 'none';
    els.canvasWrap.style.display = 'block';
    els.transport.style.display = 'flex';
  } else {
    els.emptyStage.style.display = 'flex';
    els.canvasWrap.style.display = 'none';
    els.transport.style.display = 'none';
  }
}

/* ---------------- audio track (music) ---------------- */
els.audioInput.addEventListener('change', e => setMusic(e.target.files[0]));
els.audioDropzone.addEventListener('click', ()=> els.audioInput.click());
['dragover','dragenter'].forEach(ev => els.audioDropzone.addEventListener(ev, e=>{ e.preventDefault(); els.audioDropzone.classList.add('drag'); }));
['dragleave','drop'].forEach(ev => els.audioDropzone.addEventListener(ev, e=>{ e.preventDefault(); els.audioDropzone.classList.remove('drag'); }));
els.audioDropzone.addEventListener('drop', e => setMusic(e.dataTransfer.files[0]));

function setMusic(file){
  if(!file || !file.type.startsWith('audio/')) return;
  const url = URL.createObjectURL(file);
  const a = new Audio(url);
  a.preload = 'auto';
  state.music = { url, el:a, name:file.name, volume:70, _audioNode:null };
  $('#audioEmpty').style.display = 'none';
  $('#audioControls').style.display = 'flex';
  $('#audioFileName').textContent = file.name;
  renderTimeline();
  toast(`Added music: ${file.name}`);
}
$('#rngMusicVol').addEventListener('input', e=>{
  if(!state.music) return;
  state.music.volume = +e.target.value;
  $('#valMusicVol').textContent = e.target.value + '%';
  if(state.music.el) state.music.el.volume = state.music.volume/100;
});
$('#btnRemoveAudio').addEventListener('click', ()=>{
  if(state.music && state.music.el){ state.music.el.pause(); }
  state.music = null;
  $('#audioEmpty').style.display = 'block';
  $('#audioControls').style.display = 'none';
  renderTimeline();
});
$('#rngClipVol').addEventListener('input', e=>{
  const c = getSelectedClip();
  if(!c) return;
  c.volume = +e.target.value;
  $('#valClipVol').textContent = e.target.value + '%';
});

/* ---------------- selection ---------------- */
function getSelectedClip(){ return state.clips.find(c => c.id === state.selectedClipId) || null; }
function getSelectedText(){ return state.texts.find(t => t.id === state.selectedTextId) || null; }

function selectClip(id){
  state.selectedClipId = id;
  state.selectedTextId = null;
  const c = getSelectedClip();
  updateGradePanel(c);
  updateTextPanel(null);
  renderTimeline();
  renderLayers();
  switchTab('grade');
}
function selectText(id){
  state.selectedTextId = id;
  state.selectedClipId = null;
  updateTextPanel(getSelectedText());
  updateGradePanel(null);
  renderTimeline();
  renderLayers();
  renderOverlays();
  switchTab('text');
}
function deselectAll(){
  state.selectedClipId = null; state.selectedTextId = null;
  updateGradePanel(null); updateTextPanel(null);
  renderTimeline(); renderLayers(); renderOverlays();
}

/* ---------------- grade panel ---------------- */
const gradeInputs = {
  brightness: $('#rngBrightness'), contrast: $('#rngContrast'), saturation: $('#rngSaturation'),
  temp: $('#rngTemp'), vignette: $('#rngVignette'), speed: $('#rngSpeed'),
};
function updateGradePanel(clip){
  const has = !!clip;
  $('#gradeEmpty').style.display = has ? 'none' : 'block';
  $('#gradeControls').style.display = has ? 'flex' : 'none';
  $('#rngClipVol').closest('.tabpanel')?.classList; // no-op guard
  if(!has) return;
  gradeInputs.brightness.value = clip.filters.brightness; $('#valBrightness').textContent = clip.filters.brightness+'%';
  gradeInputs.contrast.value = clip.filters.contrast; $('#valContrast').textContent = clip.filters.contrast+'%';
  gradeInputs.saturation.value = clip.filters.saturation; $('#valSaturation').textContent = clip.filters.saturation+'%';
  gradeInputs.temp.value = clip.filters.temp; $('#valTemp').textContent = clip.filters.temp;
  gradeInputs.vignette.value = clip.filters.vignette; $('#valVignette').textContent = clip.filters.vignette+'%';
  gradeInputs.speed.value = Math.round(clip.speed*100); $('#valSpeed').textContent = clip.speed.toFixed(2)+'×';
  $('#rngClipVol').value = clip.volume; $('#valClipVol').textContent = clip.volume+'%';
  $$('#presetGrid .preset-chip').forEach(p => p.classList.toggle('active', p.dataset.preset === (clip._preset||'none')));
}
Object.entries(gradeInputs).forEach(([key, input]) => {
  input.addEventListener('input', () => {
    const c = getSelectedClip(); if(!c) return;
    c._preset = 'custom';
    $$('#presetGrid .preset-chip').forEach(p => p.classList.remove('active'));
    if(key === 'speed'){
      c.speed = clamp((+input.value)/100, 0.25, 4);
      $('#valSpeed').textContent = c.speed.toFixed(2)+'×';
      recalcTimeline(); renderTimeline();
    } else {
      c.filters[key] = +input.value;
      $('#val'+key.charAt(0).toUpperCase()+key.slice(1)).textContent = input.value + (key==='temp' ? '' : '%');
    }
    renderFrame();
  });
});
$('#btnResetGrade').addEventListener('click', () => {
  const c = getSelectedClip(); if(!c) return;
  c.filters = defaultFilters(); c.speed = 1; c._preset = 'none';
  recalcTimeline(); updateGradePanel(c); renderTimeline(); renderFrame();
});
const PRESETS = {
  none:    { brightness:100, contrast:100, saturation:100, temp:0, vignette:0 },
  vivid:   { brightness:104, contrast:112, saturation:150, temp:6, vignette:8 },
  mono:    { brightness:102, contrast:112, saturation:0, temp:0, vignette:14 },
  vintage: { brightness:104, contrast:92, saturation:78, temp:22, vignette:28 },
  cold:    { brightness:98, contrast:108, saturation:88, temp:-24, vignette:10 },
  warm:    { brightness:106, contrast:104, saturation:112, temp:26, vignette:6 },
};
$$('#presetGrid .preset-chip').forEach(chip => {
  chip.addEventListener('click', () => {
    const c = getSelectedClip(); if(!c) return;
    const p = PRESETS[chip.dataset.preset];
    c.filters = { ...p };
    c._preset = chip.dataset.preset;
    updateGradePanel(c);
    renderFrame();
  });
});

/* ---------------- text layers ---------------- */
$('#btnAddText').addEventListener('click', () => {
  const t = {
    id: uid(), text:'Your text here', size:42, color:'#ffffff',
    font: "'Space Grotesk', sans-serif", x:0.5, y:0.82,
    startPct:0, endPct:100,
  };
  state.texts.push(t);
  renderLayers(); renderOverlays();
  selectText(t.id);
});
function updateTextPanel(t){
  const has = !!t;
  $('#textEmpty').style.display = has ? 'none' : 'block';
  $('#textControls').style.display = has ? 'flex' : 'none';
  if(!has) return;
  $('#txtContent').value = t.text;
  $('#rngTextSize').value = t.size; $('#valTextSize').textContent = t.size+'px';
  $$('#colorRow .swatch').forEach(s => s.classList.toggle('active', s.dataset.color === t.color));
  $('#selFont').value = t.font;
  $('#rngTextStart').value = t.startPct;
  $('#rngTextEnd').value = t.endPct;
}
$('#txtContent').addEventListener('input', e => { const t=getSelectedText(); if(!t) return; t.text = e.target.value; renderOverlays(); renderTimeline(); });
$('#rngTextSize').addEventListener('input', e => { const t=getSelectedText(); if(!t) return; t.size = +e.target.value; $('#valTextSize').textContent = t.size+'px'; renderOverlays(); });
$$('#colorRow .swatch').forEach(sw => sw.addEventListener('click', () => {
  const t = getSelectedText(); if(!t) return;
  t.color = sw.dataset.color;
  $$('#colorRow .swatch').forEach(s=>s.classList.remove('active'));
  sw.classList.add('active');
  renderOverlays();
}));
$('#selFont').addEventListener('change', e => { const t=getSelectedText(); if(!t) return; t.font = e.target.value; renderOverlays(); });
$('#rngTextStart').addEventListener('input', e => {
  const t = getSelectedText(); if(!t) return;
  t.startPct = Math.min(+e.target.value, t.endPct-1);
  e.target.value = t.startPct;
  renderTimeline(); renderOverlays();
});
$('#rngTextEnd').addEventListener('input', e => {
  const t = getSelectedText(); if(!t) return;
  t.endPct = Math.max(+e.target.value, t.startPct+1);
  e.target.value = t.endPct;
  renderTimeline(); renderOverlays();
});
$('#btnDeleteText').addEventListener('click', () => {
  const t = getSelectedText(); if(!t) return;
  state.texts = state.texts.filter(x => x.id !== t.id);
  deselectAll(); renderLayers(); renderOverlays(); renderTimeline();
});

function renderOverlays(){
  els.overlayLayer.innerHTML = '';
  const rect = els.canvas.getBoundingClientRect();
  const scaleX = rect.width / CANVAS_W, scaleY = rect.height / CANVAS_H;
  const curPct = state.totalDuration ? (state.playhead/state.totalDuration)*100 : 0;
  state.texts.forEach(t => {
    if(curPct < t.startPct || curPct > t.endPct) return;
    const div = document.createElement('div');
    div.className = 'text-overlay' + (t.id === state.selectedTextId ? ' selected' : '');
    div.style.left = (t.x*100) + '%';
    div.style.top = (t.y*100) + '%';
    div.style.fontSize = (t.size*scaleY) + 'px';
    div.style.color = t.color;
    div.style.fontFamily = t.font;
    div.textContent = t.text;
    div.addEventListener('mousedown', (e)=> startDragText(e, t));
    div.addEventListener('touchstart', (e)=> startDragText(e, t), {passive:false});
    div.addEventListener('click', (e)=>{ e.stopPropagation(); selectText(t.id); });
    els.overlayLayer.appendChild(div);
  });
}
function startDragText(e, t){
  e.preventDefault(); e.stopPropagation();
  selectText(t.id);
  const move = (ev) => {
    const point = ev.touches ? ev.touches[0] : ev;
    const rect = els.canvas.getBoundingClientRect();
    let x = (point.clientX - rect.left) / rect.width;
    let y = (point.clientY - rect.top) / rect.height;
    t.x = clamp(x, 0.02, 0.98);
    t.y = clamp(y, 0.04, 0.98);
    renderOverlays();
  };
  const up = () => {
    window.removeEventListener('mousemove', move); window.removeEventListener('mouseup', up);
    window.removeEventListener('touchmove', move); window.removeEventListener('touchend', up);
  };
  window.addEventListener('mousemove', move); window.addEventListener('mouseup', up);
  window.addEventListener('touchmove', move, {passive:false}); window.addEventListener('touchend', up);
}

/* ---------------- layers panel ---------------- */
function renderLayers(){
  els.layersList.innerHTML = '';
  const items = [
    ...state.clips.map(c => ({ type:'clip', ref:c })),
    ...state.texts.map(t => ({ type:'text', ref:t })),
  ];
  els.layersEmpty.style.display = items.length ? 'none' : 'block';
  items.forEach(it => {
    const row = document.createElement('div');
    const selected = it.type==='clip' ? it.ref.id===state.selectedClipId : it.ref.id===state.selectedTextId;
    row.style.cssText = `display:flex;align-items:center;gap:8px;padding:8px 10px;border-radius:8px;cursor:pointer;border:1px solid ${selected?'var(--teal)':'var(--line)'};background:var(--ink-800);font-size:12.5px;`;
    row.innerHTML = it.type === 'clip'
      ? `<span style="width:8px;height:8px;border-radius:2px;background:var(--violet);flex:none;"></span><span style="overflow:hidden;text-overflow:ellipsis;white-space:nowrap;">${it.ref.name}</span>`
      : `<span style="width:8px;height:8px;border-radius:2px;background:var(--teal);flex:none;"></span><span style="overflow:hidden;text-overflow:ellipsis;white-space:nowrap;">"${it.ref.text.slice(0,18)}"</span>`;
    row.addEventListener('click', () => it.type === 'clip' ? selectClip(it.ref.id) : selectText(it.ref.id));
    els.layersList.appendChild(row);
  });
}

/* ---------------- timeline rendering ---------------- */
function pxPerSec(){ return state.zoomPxPerSec; }
els.rngZoom.addEventListener('input', e => { state.zoomPxPerSec = +e.target.value; renderTimeline(); });

function renderTimeline(){
  recalcTimeline();
  const pps = pxPerSec();
  const totalW = Math.max(600, (state.totalDuration||0) * pps + 200);
  els.tlTracks.style.width = totalW + 'px';
  els.tlRuler.style.width = totalW + 'px';
  els.tlRuler.innerHTML = '';
  const step = pps < 40 ? 5 : pps < 90 ? 2 : 1;
  for(let s=0; s <= (state.totalDuration||10)+5; s += step){
    const tick = document.createElement('span');
    tick.style.left = (64 + s*pps) + 'px';
    tick.textContent = fmtTime(s).slice(0,5);
    els.tlRuler.appendChild(tick);
  }

  // video lane
  els.laneVideo.innerHTML = '';
  els.laneVideo.style.width = totalW + 'px';
  state.clips.forEach(c => {
    const el = document.createElement('div');
    el.className = 'tl-clip' + (c.id===state.selectedClipId ? ' selected':'');
    el.style.left = c.seqStart*pps + 'px';
    el.style.width = Math.max(18, c.seqDur*pps) + 'px';
    const label = document.createElement('div');
    label.className = 'clip-label';
    label.textContent = c.name + (c.speed!==1 ? ` · ${c.speed.toFixed(2)}×` : '');
    el.appendChild(label);
    const hl = document.createElement('div'); hl.className='handle l';
    const hr = document.createElement('div'); hr.className='handle r';
    el.append(hl, hr);
    el.addEventListener('mousedown', (e) => { if(e.target===hl || e.target===hr) return; startDragClip(e, c); });
    el.addEventListener('click', (e)=>{ e.stopPropagation(); selectClip(c.id); });
    hl.addEventListener('mousedown', e => startTrim(e, c, 'l'));
    hr.addEventListener('mousedown', e => startTrim(e, c, 'r'));
    els.laneVideo.appendChild(el);
  });

  // text lane
  els.laneText.innerHTML = '';
  els.laneText.style.width = totalW + 'px';
  state.texts.forEach(t => {
    const el = document.createElement('div');
    el.className = 'tl-clip text-clip' + (t.id===state.selectedTextId ? ' selected':'');
    const s = (t.startPct/100)*state.totalDuration, dur = ((t.endPct-t.startPct)/100)*state.totalDuration;
    el.style.left = s*pps + 'px';
    el.style.width = Math.max(16, dur*pps) + 'px';
    const label = document.createElement('div'); label.className='clip-label'; label.textContent = 'T · ' + t.text.slice(0,16);
    el.appendChild(label);
    el.addEventListener('click', (e)=>{ e.stopPropagation(); selectText(t.id); });
    els.laneText.appendChild(el);
  });

  // audio lane
  els.laneAudio.innerHTML = '';
  els.laneAudio.style.width = totalW + 'px';
  if(state.music){
    const el = document.createElement('div');
    el.className = 'tl-clip audio-clip';
    el.style.left = '0px';
    el.style.width = Math.max(18, state.totalDuration*pps) + 'px';
    const label = document.createElement('div'); label.className='clip-label'; label.textContent = '♪ ' + state.music.name;
    el.appendChild(label);
    els.laneAudio.appendChild(el);
  }

  positionPlayhead();
}
els.tlBody.addEventListener('click', (e) => {
  if(e.target === els.tlBody || e.target.id==='tlTracks'){ deselectAll(); }
});
els.tlRuler.addEventListener('click', (e) => {
  const rect = els.tlRuler.getBoundingClientRect();
  const x = e.clientX - rect.left - 64;
  seekTo(clamp(x/pxPerSec(), 0, state.totalDuration));
});

function positionPlayhead(){
  const x = 64 + state.playhead * pxPerSec();
  els.tlPlayhead.style.left = x + 'px';
  els.tCurrent.textContent = fmtTime(state.playhead);
}

/* ---- drag clip to reorder ---- */
function startDragClip(e, clip){
  e.preventDefault();
  selectClip(clip.id);
  const startX = e.clientX;
  const origIndex = state.clips.indexOf(clip);
  let moved = false;
  const move = (ev) => {
    if(Math.abs(ev.clientX - startX) > 20) moved = true;
    if(!moved) return;
    const laneRect = els.laneVideo.getBoundingClientRect();
    const x = ev.clientX - laneRect.left;
    let idx = 0, acc = 0;
    for(let i=0;i<state.clips.length;i++){
      const w = state.clips[i].seqDur*pxPerSec();
      if(x > acc + w/2) idx = i+1; else break;
      acc += w;
    }
    idx = clamp(idx, 0, state.clips.length-1);
    const curIdx = state.clips.indexOf(clip);
    if(idx !== curIdx){
      state.clips.splice(curIdx,1);
      state.clips.splice(idx,0,clip);
      recalcTimeline(); renderTimeline();
    }
  };
  const up = () => {
    window.removeEventListener('mousemove', move); window.removeEventListener('mouseup', up);
    renderFrame();
  };
  window.addEventListener('mousemove', move); window.addEventListener('mouseup', up);
}

/* ---- trim handles ---- */
function startTrim(e, clip, side){
  e.preventDefault(); e.stopPropagation();
  selectClip(clip.id);
  const pps = pxPerSec();
  const startX = e.clientX;
  const origIn = clip.trimIn, origOut = clip.trimOut;
  const move = (ev) => {
    const dx = (ev.clientX - startX) / pps; // seconds, in local media time (approx, ignores speed for direct manipulation feel)
    if(side==='l'){
      clip.trimIn = clamp(origIn + dx*clip.speed, 0, clip.trimOut-0.1);
    } else {
      clip.trimOut = clamp(origOut + dx*clip.speed, clip.trimIn+0.1, clip.naturalDuration);
    }
    recalcTimeline(); renderTimeline(); renderFrame();
  };
  const up = () => { window.removeEventListener('mousemove', move); window.removeEventListener('mouseup', up); };
  window.addEventListener('mousemove', move); window.addEventListener('mouseup', up);
}

/* ---------------- transport ---------------- */
function seekTo(t){
  pausePlayback();
  state.playhead = clamp(t, 0, state.totalDuration);
  renderFrame();
  positionPlayhead();
}
els.btnSplit.addEventListener('click', splitAtPlayhead);
document.addEventListener('keydown', (e) => {
  const tag = (e.target.tagName||'').toLowerCase();
  if(tag==='input' || tag==='textarea') return;
  if(e.code === 'Space'){ e.preventDefault(); togglePlay(); }
  if(e.key.toLowerCase()==='s'){ splitAtPlayhead(); }
  if(e.key === 'Delete' || e.key === 'Backspace'){ deleteSelected(); }
});
function splitAtPlayhead(){
  const c = getActiveClip(state.playhead);
  if(!c || c.kind!=='video' && c.kind!=='image') return;
  const local = localTimeFor(c, state.playhead);
  if(local - c.trimIn < 0.15 || c.trimOut - local < 0.15) { toast('Move the playhead further into the clip to split'); return; }
  const idx = state.clips.indexOf(c);
  const clone = { ...c, id: uid(), trimIn: local, filters:{...c.filters} };
  c.trimOut = local;
  state.clips.splice(idx+1, 0, clone);
  recalcTimeline(); renderTimeline(); renderLayers(); renderFrame();
  toast('Split clip');
}
els.btnDeleteClip.addEventListener('click', deleteSelected);
function deleteSelected(){
  if(state.selectedClipId){
    state.clips = state.clips.filter(c => c.id !== state.selectedClipId);
    state.selectedClipId = null;
    recalcTimeline(); renderTimeline(); renderLayers(); showStage(); renderFrame();
  } else if(state.selectedTextId){
    state.texts = state.texts.filter(t => t.id !== state.selectedTextId);
    state.selectedTextId = null;
    renderTimeline(); renderLayers(); renderOverlays();
  }
}

function togglePlay(){ state.playing ? pausePlayback() : startPlayback(); }
els.btnPlay.addEventListener('click', togglePlay);
function playIcon(playing){
  els.iconPlay.innerHTML = playing
    ? '<rect x="6" y="5" width="4" height="14" rx="1"/><rect x="14" y="5" width="4" height="14" rx="1"/>'
    : '<path d="M8 5v14l11-7z"/>';
}
function startPlayback(){
  if(state.clips.length===0) return;
  if(state.playhead >= state.totalDuration) state.playhead = 0;
  state.playing = true;
  playIcon(true);
  lastFrameTs = performance.now();
  if(state.music){
    try{
      state.music.el.currentTime = state.playhead % Math.max(0.01, state.music.el.duration || state.totalDuration);
      state.music.el.volume = state.music.volume/100;
      state.music.el.play().catch(()=>{});
    }catch(_e){}
  }
  rafId = requestAnimationFrame(playLoop);
}
function pausePlayback(){
  state.playing = false;
  playIcon(false);
  if(rafId) cancelAnimationFrame(rafId);
  if(state.music && state.music.el) state.music.el.pause();
}
function playLoop(ts){
  if(!state.playing) return;
  const dt = Math.min(0.05, (ts - lastFrameTs)/1000);
  lastFrameTs = ts;
  state.playhead += dt;
  if(state.playhead >= state.totalDuration){
    state.playhead = state.totalDuration;
    renderFrame(); positionPlayhead();
    pausePlayback();
    return;
  }
  renderFrame();
  positionPlayhead();
  rafId = requestAnimationFrame(playLoop);
}

/* ---------------- rendering a frame ---------------- */
function filterString(f){
  const sepia = f.temp > 0 ? clamp(f.temp/100, 0, 0.4) : 0;
  const hue = f.temp < 0 ? clamp(-f.temp*0.9, 0, 40) : 0;
  return `brightness(${f.brightness}%) contrast(${f.contrast}%) saturate(${f.saturation}%) sepia(${sepia}) hue-rotate(${hue}deg)`;
}
function drawVignette(amount){
  if(!amount) return;
  const g = ctx.createRadialGradient(CANVAS_W/2, CANVAS_H/2, CANVAS_H*0.35, CANVAS_W/2, CANVAS_H/2, CANVAS_H*0.85);
  g.addColorStop(0, 'rgba(0,0,0,0)');
  g.addColorStop(1, `rgba(0,0,0,${(amount/100)*0.7})`);
  ctx.save();
  ctx.fillStyle = g;
  ctx.fillRect(0,0,CANVAS_W,CANVAS_H);
  ctx.restore();
}
function drawClipFrame(c, seqTime){
  const local = localTimeFor(c, seqTime);
  ctx.save();
  ctx.filter = filterString(c.filters);
  if(c.kind === 'video'){
    if(Math.abs(c.el.currentTime - local) > 0.06 && c.el.readyState >= 2){
      try{ c.el.currentTime = local; }catch(_e){}
    }
    try{ drawCover(c.el, c.el.videoWidth||CANVAS_W, c.el.videoHeight||CANVAS_H); }catch(_e){}
  } else {
    drawCover(c.el, c.el.naturalWidth||CANVAS_W, c.el.naturalHeight||CANVAS_H);
  }
  ctx.restore();
  drawVignette(c.filters.vignette);
}
function drawCover(source, sw, sh){
  const scale = Math.max(CANVAS_W/sw, CANVAS_H/sh);
  const dw = sw*scale, dh = sh*scale;
  const dx = (CANVAS_W-dw)/2, dy = (CANVAS_H-dh)/2;
  ctx.drawImage(source, dx, dy, dw, dh);
}
function renderFrame(){
  ctx.fillStyle = '#000';
  ctx.fillRect(0,0,CANVAS_W,CANVAS_H);
  const c = getActiveClip(state.playhead);
  if(c) drawClipFrame(c, state.playhead);
  renderOverlays();
}

/* ---------------- tabs ---------------- */
function switchTab(name){
  $$('.tab-btn').forEach(b => b.classList.toggle('active', b.dataset.tab===name));
  $$('.tabpanel').forEach(p => p.classList.toggle('active', p.dataset.panel===name));
}
$$('.tab-btn').forEach(btn => btn.addEventListener('click', () => switchTab(btn.dataset.tab)));

/* mobile panel switching */
$('#mobShowLeft')?.addEventListener('click', ()=>{
  $('#panelLeft').classList.add('mobile-active'); $('#panelRight').classList.remove('mobile-active');
});
$('#mobShowRight')?.addEventListener('click', ()=>{
  $('#panelRight').classList.add('mobile-active'); $('#panelLeft').classList.remove('mobile-active');
});

/* ---------------- export ---------------- */
els.btnExport.addEventListener('click', () => {
  if(state.clips.length===0){ toast('Add a clip before exporting'); return; }
  els.exportModal.classList.add('show');
  els.exportSetup.style.display = 'block';
  els.exportProgress.style.display = 'none';
  els.btnStartExport.style.display = 'inline-flex';
});
els.btnCancelExport.addEventListener('click', () => els.exportModal.classList.remove('show'));

els.btnStartExport.addEventListener('click', runExport);

async function runExport(){
  pausePlayback();
  const [w,h] = els.selRes.value.split('x').map(Number);
  els.exportSetup.style.display = 'none';
  els.exportProgress.style.display = 'block';
  els.btnStartExport.style.display = 'none';

  const exportCanvas = document.createElement('canvas');
  exportCanvas.width = w; exportCanvas.height = h;
  const ex = exportCanvas.getContext('2d');

  let audioCtx, dest, mixed = false;
  try{
    audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    dest = audioCtx.createMediaStreamDestination();
    if(state.music){
      const src = audioCtx.createMediaElementSource(state.music.el);
      const gain = audioCtx.createGain();
      gain.gain.value = state.music.volume/100;
      src.connect(gain).connect(dest);
    }
    state.clips.forEach(c => {
      if(c.kind !== 'video' || c.muted) return;
      try{
        const src = audioCtx.createMediaElementSource(c.el);
        const gain = audioCtx.createGain();
        gain.gain.value = c.volume/100;
        src.connect(gain).connect(dest);
        c._exportGain = gain;
      }catch(_e){ /* element may already be connected */ }
    });
    mixed = true;
  }catch(err){
    console.warn('Audio mix unavailable, exporting video only', err);
  }

  const canvasStream = exportCanvas.captureStream(30);
  const tracks = [...canvasStream.getVideoTracks()];
  if(mixed && dest) tracks.push(...dest.stream.getAudioTracks());
  const finalStream = new MediaStream(tracks);

  let mimeType = 'video/webm;codecs=vp9,opus';
  if(!MediaRecorder.isTypeSupported(mimeType)) mimeType = 'video/webm;codecs=vp8,opus';
  if(!MediaRecorder.isTypeSupported(mimeType)) mimeType = 'video/webm';

  const recorder = new MediaRecorder(finalStream, { mimeType, videoBitsPerSecond: 6_000_000 });
  const chunks = [];
  recorder.ondataavailable = e => { if(e.data.size>0) chunks.push(e.data); };

  const finished = new Promise(resolve => { recorder.onstop = resolve; });
  recorder.start();

  if(state.music){ try{ state.music.el.currentTime = 0; state.music.el.volume = state.music.volume/100; await state.music.el.play(); }catch(_e){} }

  function drawExportOverlays(seqTime){
    const curPct = state.totalDuration ? (seqTime/state.totalDuration)*100 : 0;
    state.texts.forEach(t => {
      if(curPct < t.startPct || curPct > t.endPct) return;
      ex.save();
      ex.font = `700 ${t.size * (h/CANVAS_H)}px ${t.font}`;
      ex.fillStyle = t.color;
      ex.textAlign = 'center';
      ex.textBaseline = 'middle';
      ex.shadowColor = 'rgba(0,0,0,0.6)';
      ex.shadowBlur = 10;
      const lines = t.text.split('\n');
      const lh = t.size*(h/CANVAS_H)*1.2;
      lines.forEach((line,i)=> ex.fillText(line, t.x*w, t.y*h + (i-(lines.length-1)/2)*lh));
      ex.restore();
    });
  }
  function exFilterString(f){ return filterString(f); }
  function exDrawCover(source, sw, sh2){
    const scale = Math.max(w/sw, h/sh2);
    const dw = sw*scale, dh = sh2*scale;
    ex.drawImage(source, (w-dw)/2, (h-dh)/2, dw, dh);
  }
  function exDrawVignette(amount){
    if(!amount) return;
    const g = ex.createRadialGradient(w/2,h/2,h*0.35, w/2,h/2,h*0.85);
    g.addColorStop(0,'rgba(0,0,0,0)'); g.addColorStop(1, `rgba(0,0,0,${(amount/100)*0.7})`);
    ex.fillStyle = g; ex.fillRect(0,0,w,h);
  }

  for(let i=0;i<state.clips.length;i++){
    const c = state.clips[i];
    els.progressLabel.textContent = `Rendering clip ${i+1} of ${state.clips.length}…`;
    if(c.kind === 'video'){
      c.el.currentTime = c.trimIn;
      c.el.playbackRate = c.speed;
      c.el.muted = c.muted;
      c.el.volume = c.muted ? 0 : (c.volume/100);
      await c.el.play().catch(()=>{});
      await new Promise(resolve => {
        function step(){
          if(c.el.paused || c.el.currentTime >= c.trimOut - 0.02 || c.el.ended){
            c.el.pause();
            resolve();
            return;
          }
          ex.fillStyle = '#000'; ex.fillRect(0,0,w,h);
          ex.save(); ex.filter = exFilterString(c.filters);
          exDrawCover(c.el, c.el.videoWidth||w, c.el.videoHeight||h);
          ex.restore();
          exDrawVignette(c.filters.vignette);
          const seqTime = c.seqStart + (c.el.currentTime - c.trimIn)/c.speed;
          drawExportOverlays(seqTime);
          const pct = clamp((seqTime/state.totalDuration)*100, 0, 100);
          els.progressFill.style.width = pct + '%';
          requestAnimationFrame(step);
        }
        step();
      });
    } else {
      const dur = c.seqDur;
      const start = performance.now();
      await new Promise(resolve => {
        function step(){
          const elapsed = (performance.now()-start)/1000;
          if(elapsed >= dur){ resolve(); return; }
          ex.fillStyle = '#000'; ex.fillRect(0,0,w,h);
          ex.save(); ex.filter = exFilterString(c.filters);
          exDrawCover(c.el, c.el.naturalWidth||w, c.el.naturalHeight||h);
          ex.restore();
          exDrawVignette(c.filters.vignette);
          const seqTime = c.seqStart + elapsed;
          drawExportOverlays(seqTime);
          const pct = clamp((seqTime/state.totalDuration)*100, 0, 100);
          els.progressFill.style.width = pct + '%';
          requestAnimationFrame(step);
        }
        step();
      });
    }
  }

  els.progressFill.style.width = '100%';
  els.progressLabel.textContent = 'Finishing up…';
  if(state.music) state.music.el.pause();
  recorder.stop();
  await finished;
  if(audioCtx) audioCtx.close().catch(()=>{});

  const blob = new Blob(chunks, { type:'video/webm' });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = (els.projName.value || 'vull_export') + '.webm';
  document.body.appendChild(a); a.click(); a.remove();
  setTimeout(()=> URL.revokeObjectURL(url), 8000);

  els.progressLabel.textContent = 'Done — check your downloads.';
  toast('Export complete');
  setTimeout(()=> els.exportModal.classList.remove('show'), 900);
  renderFrame();
}

/* ---------------- PWA install ---------------- */
let deferredPrompt = null;
window.addEventListener('beforeinstallprompt', (e) => {
  e.preventDefault();
  deferredPrompt = e;
});
els.btnInstall.addEventListener('click', async () => {
  if(deferredPrompt){
    deferredPrompt.prompt();
    await deferredPrompt.userChoice;
    deferredPrompt = null;
  } else {
    toast('Use your browser menu → "Install app" or "Add to Home Screen"');
  }
});
if('serviceWorker' in navigator){
  window.addEventListener('load', () => { navigator.serviceWorker.register('sw.js').catch(()=>{}); });
}

/* ---------------- init ---------------- */
window.addEventListener('resize', () => { renderOverlays(); });
recalcTimeline();
renderTimeline();
renderLayers();
showStage();
playIcon(false);

})();
