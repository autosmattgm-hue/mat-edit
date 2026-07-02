(function(){
"use strict";

/* ============================================================
   VULL EDITOR — core engine v2
   Video track drives sequence length. Text + stickers + audio
   overlay it. Preview uses scrub-seek compositing with a live
   transition renderer (crossfade / slide / wipe / zoom) and an
   optional per-clip chroma key. Export uses real playback through
   a MediaRecorder + Web Audio mix so clip/track audio actually
   makes it into the file, with a frozen-frame transition blend
   at clip boundaries.
   ============================================================ */

const ASPECTS = {
  '16:9': [1280, 720],
  '9:16': [720, 1280],
  '1:1':  [1080, 1080],
  '4:5':  [864, 1080],
};
const RES_PRESETS = {
  '16:9': [[1280,720,'HD'],[1920,1080,'Full HD'],[854,480,'SD']],
  '9:16': [[720,1280,'HD'],[1080,1920,'Full HD'],[480,854,'SD']],
  '1:1':  [[1080,1080,'HD square'],[720,720,'SD square']],
  '4:5':  [[1080,1350,'HD portrait'],[864,1080,'SD portrait']],
};
const IMAGE_DEFAULT_DURATION = 4; // seconds, at speed 1
const EMOJIS = ['😀','😂','🥳','😍','🔥','✨','💯','🎉','❤️','👍','👏','🙌','😎','🤔','😢','💪','⭐','☀️','🌈','🎬','📸','🎵','⚡','💥'];

let CANVAS_W = 1280, CANVAS_H = 720;

const $ = (sel, root=document) => root.querySelector(sel);
const $$ = (sel, root=document) => Array.from(root.querySelectorAll(sel));
const uid = () => Math.random().toString(36).slice(2,10);
const clamp = (v,a,b) => Math.max(a, Math.min(b, v));
const hexToRgb = (hex) => {
  const m = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
  return m ? [parseInt(m[1],16), parseInt(m[2],16), parseInt(m[3],16)] : [0,255,0];
};

const els = {
  fileInput: $('#fileInput'), dropzone: $('#dropzone'), mediaGrid: $('#mediaGrid'),
  audioInput: $('#audioInput'), audioDropzone: $('#audioDropzone'),
  canvas: $('#previewCanvas'), canvasWrap: $('#canvasWrap'), emptyStage: $('#emptyStage'),
  overlayLayer: $('#overlayLayer'), transport: $('#transport'),
  btnPlay: $('#btnPlay'), iconPlay: $('#iconPlay'),
  tCurrent: $('#tCurrent'), tTotal: $('#tTotal'),
  btnSplit: $('#btnSplit'), btnDeleteClip: $('#btnDeleteClip'), btnDuplicateClip: $('#btnDuplicateClip'),
  tlTracks: $('#tlTracks'), tlRuler: $('#tlRuler'), tlPlayhead: $('#tlPlayhead'), tlBody: $('#tlBody'),
  laneVideo: $('#laneVideo'), laneText: $('#laneText'), laneAudio: $('#laneAudio'), laneStickers: $('#laneStickers'),
  rngZoom: $('#rngZoom'), chkSnap: $('#chkSnap'),
  layersList: $('#layersList'), layersEmpty: $('#layersEmpty'),
  toast: $('#toast'),
  btnExport: $('#btnExport'), exportModal: $('#exportModal'), btnStartExport: $('#btnStartExport'),
  btnCancelExport: $('#btnCancelExport'), exportSetup: $('#exportSetup'), exportProgress: $('#exportProgress'),
  progressFill: $('#progressFill'), progressLabel: $('#progressLabel'),
  selRes: $('#selRes'), selFps: $('#selFps'), selQuality: $('#selQuality'), selFormat: $('#selFormat'),
  btnInstall: $('#btnInstall'), projName: $('#projName'),
  btnEmptyImport: $('#btnEmptyImport'), btnUndo: $('#btnUndo'), btnRedo: $('#btnRedo'),
  aspectSwitch: $('#aspectSwitch'),
};
let ctx = els.canvas.getContext('2d');

/* ---------------- state ---------------- */
const state = {
  clips: [],        // video track
  texts: [],        // text overlays
  stickers: [],      // emoji / shape overlays
  music: null,       // {url, el, name, volume, fade, duck}
  playhead: 0,
  playing: false,
  selectedClipId: null,
  selectedTextId: null,
  selectedStickerId: null,
  zoomPxPerSec: 70,
  totalDuration: 0,
  aspect: '16:9',
};
const clipPool = new Map(); // id -> clip object, survives removal for undo/redo

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
function defaultFilters(){
  return { brightness:100, contrast:100, saturation:100, temp:0, exposure:0, hue:0, vignette:0, blur:0, sharpen:0, grain:0 };
}
function defaultChroma(){
  return { enabled:false, color:'#00ff66', similarity:40, smoothness:20 };
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

/* ---------------- undo / redo ---------------- */
let historyStack = [], redoStack = [];
function snapshot(){
  return {
    clipOrder: state.clips.map(c => ({
      id:c.id, trimIn:c.trimIn, trimOut:c.trimOut, speed:c.speed, filters:{...c.filters},
      volume:c.volume, muted:c.muted, _preset:c._preset,
      transitionType:c.transitionType, transitionDur:c.transitionDur,
      chroma:{...c.chroma},
    })),
    texts: JSON.parse(JSON.stringify(state.texts)),
    stickers: JSON.parse(JSON.stringify(state.stickers)),
    music: state.music ? { volume: state.music.volume, fade: state.music.fade, duck: state.music.duck } : null,
    aspect: state.aspect,
  };
}
function restoreSnapshot(snap){
  state.clips = snap.clipOrder.map(rec => {
    const c = clipPool.get(rec.id);
    if(!c) return null;
    Object.assign(c, {
      trimIn:rec.trimIn, trimOut:rec.trimOut, speed:rec.speed, filters:{...rec.filters},
      volume:rec.volume, muted:rec.muted, _preset:rec._preset,
      transitionType:rec.transitionType, transitionDur:rec.transitionDur, chroma:{...rec.chroma},
    });
    return c;
  }).filter(Boolean);
  state.texts = snap.texts;
  state.stickers = snap.stickers;
  if(state.music && snap.music){ state.music.volume=snap.music.volume; state.music.fade=snap.music.fade; state.music.duck=snap.music.duck; }
  if(snap.aspect !== state.aspect) applyAspect(snap.aspect);
  state.selectedClipId = null; state.selectedTextId = null; state.selectedStickerId = null;
  recalcTimeline(); renderTimeline(); renderLayers(); renderFrame(); renderOverlays(); showStage();
  updateGradePanel(null); updateFxPanel(null); updateTextPanel(null); updateStickerPanel(null);
  updateUndoRedoButtons();
}
function pushUndo(){
  historyStack.push(snapshot());
  if(historyStack.length > 60) historyStack.shift();
  redoStack.length = 0;
  updateUndoRedoButtons();
}
function undo(){
  if(!historyStack.length) return;
  redoStack.push(snapshot());
  restoreSnapshot(historyStack.pop());
}
function redo(){
  if(!redoStack.length) return;
  historyStack.push(snapshot());
  restoreSnapshot(redoStack.pop());
}
function updateUndoRedoButtons(){
  els.btnUndo.disabled = historyStack.length === 0;
  els.btnRedo.disabled = redoStack.length === 0;
}
els.btnUndo.addEventListener('click', undo);
els.btnRedo.addEventListener('click', redo);
function undoableRange(el){
  let committed = false;
  const start = () => { if(!committed){ pushUndo(); committed = true; } };
  el.addEventListener('pointerdown', start);
  el.addEventListener('mousedown', start);
  el.addEventListener('touchstart', start, {passive:true});
  el.addEventListener('change', () => { committed = false; });
}

/* ---------------- aspect ratio ---------------- */
function applyAspect(aspect){
  state.aspect = aspect;
  const [w,h] = ASPECTS[aspect];
  CANVAS_W = w; CANVAS_H = h;
  els.canvas.width = w; els.canvas.height = h;
  $$('.aspect-btn').forEach(b => b.classList.toggle('active', b.dataset.aspect === aspect));
  renderFrame(); renderOverlays();
}
$$('.aspect-btn').forEach(btn => btn.addEventListener('click', () => {
  if(btn.dataset.aspect === state.aspect) return;
  pushUndo();
  applyAspect(btn.dataset.aspect);
  toast(`Canvas set to ${btn.dataset.aspect}`);
}));

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
          seqStart:0, seqDur:0, _audioNode:null,
          transitionType:'none', transitionDur:0.6, chroma: defaultChroma(),
        };
        clipPool.set(clip.id, clip);
        pushUndo();
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
          transitionType:'none', transitionDur:0.6, chroma: defaultChroma(),
        };
        clipPool.set(clip.id, clip);
        pushUndo();
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
  item.title = 'Click to add another copy to the timeline';
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
  item.addEventListener('click', () => addCopyToTimeline(clip));
  els.mediaGrid.appendChild(item);
}
function addCopyToTimeline(sourceClip){
  pushUndo();
  const clone = { ...sourceClip, id: uid(), filters: defaultFilters(), chroma: defaultChroma(),
    trimIn:0, trimOut: sourceClip.naturalDuration, speed:1, seqStart:0, seqDur:0,
    transitionType:'none', transitionDur:0.6, _preset:'none' };
  clipPool.set(clone.id, clone);
  state.clips.push(clone);
  recalcTimeline(); renderTimeline(); renderLayers(); renderFrame();
  selectClip(clone.id);
  toast(`Added another ${sourceClip.name}`);
}

els.fileInput.addEventListener('change', e => acceptFiles(e.target.files));
els.dropzone.addEventListener('click', () => els.fileInput.click());
['dragover','dragenter'].forEach(ev => els.dropzone.addEventListener(ev, e=>{ e.preventDefault(); els.dropzone.classList.add('drag'); }));
['dragleave','drop'].forEach(ev => els.dropzone.addEventListener(ev, e=>{ e.preventDefault(); els.dropzone.classList.remove('drag'); }));
els.dropzone.addEventListener('drop', e => acceptFiles(e.dataTransfer.files));
els.btnEmptyImport.addEventListener('click', () => els.fileInput.click());

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
  pushUndo();
  const url = URL.createObjectURL(file);
  const a = new Audio(url);
  a.preload = 'auto';
  state.music = { url, el:a, name:file.name, volume:70, fade:0.5, duck:true, _audioNode:null };
  $('#audioEmpty').style.display = 'none';
  $('#audioControls').style.display = 'flex';
  $('#audioFileName').textContent = file.name;
  renderTimeline();
  toast(`Added music: ${file.name}`);
}
const rngMusicVol = $('#rngMusicVol'); undoableRange(rngMusicVol);
rngMusicVol.addEventListener('input', e=>{
  if(!state.music) return;
  state.music.volume = +e.target.value;
  $('#valMusicVol').textContent = e.target.value + '%';
});
const chkDuck = $('#chkDuck');
chkDuck.addEventListener('change', e=>{ if(state.music){ pushUndo(); state.music.duck = e.target.checked; } });
const rngMusicFade = $('#rngMusicFade'); undoableRange(rngMusicFade);
rngMusicFade.addEventListener('input', e=>{
  if(!state.music) return;
  state.music.fade = (+e.target.value)/10;
  $('#valMusicFade').textContent = state.music.fade.toFixed(1) + 's';
});
$('#btnRemoveAudio').addEventListener('click', ()=>{
  pushUndo();
  if(state.music && state.music.el){ state.music.el.pause(); }
  state.music = null;
  $('#audioEmpty').style.display = 'block';
  $('#audioControls').style.display = 'none';
  renderTimeline();
});
const rngClipVol = $('#rngClipVol'); undoableRange(rngClipVol);
rngClipVol.addEventListener('input', e=>{
  const c = getSelectedClip();
  if(!c) return;
  c.volume = +e.target.value;
  $('#valClipVol').textContent = e.target.value + '%';
});
function updateMusicVolume(){
  if(!state.music) return;
  const t = state.playhead;
  const total = state.totalDuration;
  const fadeSec = state.music.fade || 0;
  let mult = 1;
  if(fadeSec > 0 && total > 0){
    if(t < fadeSec) mult = t/fadeSec;
    else if(t > total - fadeSec) mult = Math.max(0, (total - t)/fadeSec);
  }
  if(state.music.duck){
    const active = getActiveClip(t);
    if(active && active.kind === 'video' && !active.muted && active.volume > 0) mult *= 0.35;
  }
  state.music.el.volume = clamp((state.music.volume/100) * mult, 0, 1);
}

/* ---------------- selection ---------------- */
function getSelectedClip(){ return state.clips.find(c => c.id === state.selectedClipId) || null; }
function getSelectedText(){ return state.texts.find(t => t.id === state.selectedTextId) || null; }
function getSelectedSticker(){ return state.stickers.find(s => s.id === state.selectedStickerId) || null; }

function selectClip(id){
  state.selectedClipId = id;
  state.selectedTextId = null;
  state.selectedStickerId = null;
  const c = getSelectedClip();
  updateGradePanel(c);
  updateFxPanel(c);
  updateTextPanel(null);
  updateStickerPanel(null);
  renderTimeline();
  renderLayers();
  switchTab('grade');
}
function selectText(id){
  state.selectedTextId = id;
  state.selectedClipId = null;
  state.selectedStickerId = null;
  updateTextPanel(getSelectedText());
  updateGradePanel(null);
  updateFxPanel(null);
  updateStickerPanel(null);
  renderTimeline();
  renderLayers();
  renderOverlays();
  switchTab('text');
}
function selectSticker(id){
  state.selectedStickerId = id;
  state.selectedClipId = null;
  state.selectedTextId = null;
  updateStickerPanel(getSelectedSticker());
  updateGradePanel(null);
  updateFxPanel(null);
  updateTextPanel(null);
  renderTimeline();
  renderLayers();
  renderOverlays();
  switchTab('stickers');
}
function deselectAll(){
  state.selectedClipId = null; state.selectedTextId = null; state.selectedStickerId = null;
  updateGradePanel(null); updateFxPanel(null); updateTextPanel(null); updateStickerPanel(null);
  renderTimeline(); renderLayers(); renderOverlays();
}

/* ---------------- grade panel ---------------- */
const gradeInputs = {
  brightness: $('#rngBrightness'), contrast: $('#rngContrast'), saturation: $('#rngSaturation'),
  exposure: $('#rngExposure'), temp: $('#rngTemp'), hue: $('#rngHue'), vignette: $('#rngVignette'), speed: $('#rngSpeed'),
};
Object.values(gradeInputs).forEach(undoableRange);
const selTransition = $('#selTransition'), rngTransDur = $('#rngTransDur');
undoableRange(rngTransDur);

function updateGradePanel(clip){
  const has = !!clip;
  $('#gradeEmpty').style.display = has ? 'none' : 'block';
  $('#gradeControls').style.display = has ? 'flex' : 'none';
  if(!has) return;
  gradeInputs.brightness.value = clip.filters.brightness; $('#valBrightness').textContent = clip.filters.brightness+'%';
  gradeInputs.contrast.value = clip.filters.contrast; $('#valContrast').textContent = clip.filters.contrast+'%';
  gradeInputs.saturation.value = clip.filters.saturation; $('#valSaturation').textContent = clip.filters.saturation+'%';
  gradeInputs.exposure.value = clip.filters.exposure; $('#valExposure').textContent = clip.filters.exposure;
  gradeInputs.temp.value = clip.filters.temp; $('#valTemp').textContent = clip.filters.temp;
  gradeInputs.hue.value = clip.filters.hue; $('#valHue').textContent = clip.filters.hue+'°';
  gradeInputs.vignette.value = clip.filters.vignette; $('#valVignette').textContent = clip.filters.vignette+'%';
  gradeInputs.speed.value = Math.round(clip.speed*100); $('#valSpeed').textContent = clip.speed.toFixed(2)+'×';
  $('#rngClipVol').value = clip.volume; $('#valClipVol').textContent = clip.volume+'%';
  $$('#presetGrid .preset-chip').forEach(p => p.classList.toggle('active', p.dataset.preset === (clip._preset||'none')));

  const idx = state.clips.indexOf(clip);
  const hasPrev = idx > 0;
  selTransition.disabled = !hasPrev;
  rngTransDur.disabled = !hasPrev;
  selTransition.value = hasPrev ? clip.transitionType : 'none';
  rngTransDur.value = Math.round((clip.transitionDur||0.6)*10);
  $('#valTransDur').textContent = (clip.transitionDur||0.6).toFixed(1)+'s';
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
      const suffix = (key==='temp'||key==='exposure') ? '' : (key==='hue' ? '°' : '%');
      $('#val'+key.charAt(0).toUpperCase()+key.slice(1)).textContent = input.value + suffix;
    }
    renderFrame();
  });
});
$('#btnResetGrade').addEventListener('click', () => {
  const c = getSelectedClip(); if(!c) return;
  pushUndo();
  c.filters = defaultFilters(); c.speed = 1; c._preset = 'none';
  recalcTimeline(); updateGradePanel(c); renderTimeline(); renderFrame();
});
const PRESETS = {
  none:        { brightness:100, contrast:100, saturation:100, temp:0,  vignette:0,  exposure:0, hue:0 },
  vivid:       { brightness:104, contrast:112, saturation:150, temp:6,  vignette:8,  exposure:4,  hue:0 },
  mono:        { brightness:102, contrast:112, saturation:0,   temp:0,  vignette:14, exposure:0,  hue:0 },
  vintage:     { brightness:104, contrast:92,  saturation:78,  temp:22, vignette:28, exposure:0,  hue:0 },
  cold:        { brightness:98,  contrast:108, saturation:88,  temp:-24,vignette:10, exposure:0,  hue:0 },
  warm:        { brightness:106, contrast:104, saturation:112, temp:26, vignette:6,  exposure:0,  hue:0 },
  filmic:      { brightness:98,  contrast:118, saturation:92,  temp:8,  vignette:22, exposure:-4, hue:0 },
  noir:        { brightness:94,  contrast:130, saturation:4,   temp:0,  vignette:38, exposure:-6, hue:0 },
  pastel:      { brightness:110, contrast:88,  saturation:70,  temp:8,  vignette:0,  exposure:6,  hue:0 },
  cinered:     { brightness:100, contrast:116, saturation:118, temp:14, vignette:18, exposure:0,  hue:-6 },
  teal_orange: { brightness:102, contrast:120, saturation:128, temp:10, vignette:14, exposure:0,  hue:8 },
  dream:       { brightness:112, contrast:86,  saturation:112, temp:16, vignette:4,  exposure:8,  hue:0 },
};
$$('#presetGrid .preset-chip').forEach(chip => {
  chip.addEventListener('click', () => {
    const c = getSelectedClip(); if(!c) return;
    pushUndo();
    const p = PRESETS[chip.dataset.preset];
    c.filters = { ...defaultFilters(), ...p };
    c._preset = chip.dataset.preset;
    updateGradePanel(c);
    renderFrame();
  });
});
selTransition.addEventListener('change', e => {
  const c = getSelectedClip(); if(!c) return;
  pushUndo();
  c.transitionType = e.target.value;
  renderTimeline(); renderFrame();
});
rngTransDur.addEventListener('input', e => {
  const c = getSelectedClip(); if(!c) return;
  c.transitionDur = clamp((+e.target.value)/10, 0.2, 2.0);
  $('#valTransDur').textContent = c.transitionDur.toFixed(1)+'s';
  renderFrame();
});

/* ---------------- effects panel (blur / sharpen / grain / chroma) ---------------- */
const fxInputs = { blur: $('#rngBlur'), sharpen: $('#rngSharpen'), grain: $('#rngGrain') };
Object.values(fxInputs).forEach(undoableRange);
const chkChroma = $('#chkChroma'), chromaControls = $('#chromaControls');
const rngChromaSim = $('#rngChromaSim'), rngChromaSmooth = $('#rngChromaSmooth');
undoableRange(rngChromaSim); undoableRange(rngChromaSmooth);

function updateFxPanel(clip){
  const has = !!clip;
  $('#fxEmpty').style.display = has ? 'none' : 'block';
  $('#fxControls').style.display = has ? 'flex' : 'none';
  if(!has) return;
  fxInputs.blur.value = clip.filters.blur; $('#valBlur').textContent = clip.filters.blur+'px';
  fxInputs.sharpen.value = clip.filters.sharpen; $('#valSharpen').textContent = clip.filters.sharpen+'%';
  fxInputs.grain.value = clip.filters.grain; $('#valGrain').textContent = clip.filters.grain+'%';
  chkChroma.checked = clip.chroma.enabled;
  chromaControls.style.display = clip.chroma.enabled ? 'flex' : 'none';
  $$('#chromaColorRow .swatch').forEach(s => s.classList.toggle('active', s.dataset.color === clip.chroma.color));
  rngChromaSim.value = clip.chroma.similarity; $('#valChromaSim').textContent = clip.chroma.similarity+'%';
  rngChromaSmooth.value = clip.chroma.smoothness; $('#valChromaSmooth').textContent = clip.chroma.smoothness+'%';
}
Object.entries(fxInputs).forEach(([key, input]) => {
  input.addEventListener('input', () => {
    const c = getSelectedClip(); if(!c) return;
    c.filters[key] = +input.value;
    $('#val'+key.charAt(0).toUpperCase()+key.slice(1)).textContent = input.value + (key==='blur'?'px':'%');
    renderFrame();
  });
});
chkChroma.addEventListener('change', e => {
  const c = getSelectedClip(); if(!c) return;
  pushUndo();
  c.chroma.enabled = e.target.checked;
  chromaControls.style.display = c.chroma.enabled ? 'flex' : 'none';
  renderFrame();
});
$$('#chromaColorRow .swatch').forEach(sw => sw.addEventListener('click', () => {
  const c = getSelectedClip(); if(!c) return;
  pushUndo();
  c.chroma.color = sw.dataset.color;
  $$('#chromaColorRow .swatch').forEach(s=>s.classList.remove('active'));
  sw.classList.add('active');
  renderFrame();
}));
rngChromaSim.addEventListener('input', e => {
  const c = getSelectedClip(); if(!c) return;
  c.chroma.similarity = +e.target.value; $('#valChromaSim').textContent = e.target.value+'%';
  renderFrame();
});
rngChromaSmooth.addEventListener('input', e => {
  const c = getSelectedClip(); if(!c) return;
  c.chroma.smoothness = +e.target.value; $('#valChromaSmooth').textContent = e.target.value+'%';
  renderFrame();
});

/* ---------------- text layers ---------------- */
$('#btnAddText').addEventListener('click', () => {
  pushUndo();
  const t = {
    id: uid(), text:'Your text here', size:42, color:'#ffffff',
    font: "'Space Grotesk', sans-serif", x:0.5, y:0.82,
    startPct:0, endPct:100, bold:false, italic:false, outline:false,
    opacity:100, rotate:0, anim:'none',
  };
  state.texts.push(t);
  renderLayers(); renderOverlays(); renderTimeline();
  selectText(t.id);
});
function updateTextPanel(t){
  const has = !!t;
  $('#textEmpty').style.display = has ? 'none' : 'block';
  $('#textControls').style.display = has ? 'flex' : 'none';
  if(!has) return;
  $('#txtContent').value = t.text;
  $('#rngTextSize').value = t.size; $('#valTextSize').textContent = t.size+'px';
  $('#rngTextOpacity').value = t.opacity; $('#valTextOpacity').textContent = t.opacity+'%';
  $('#rngTextRotate').value = t.rotate; $('#valTextRotate').textContent = t.rotate+'°';
  $$('#colorRow .swatch').forEach(s => s.classList.toggle('active', s.dataset.color === t.color));
  $('#selFont').value = t.font;
  $('#selTextAnim').value = t.anim;
  $('#rngTextStart').value = t.startPct;
  $('#rngTextEnd').value = t.endPct;
  $('#btnBold').classList.toggle('active', t.bold);
  $('#btnItalic').classList.toggle('active', t.italic);
  $('#btnOutline').classList.toggle('active', t.outline);
}
$('#txtContent').addEventListener('input', e => { const t=getSelectedText(); if(!t) return; t.text = e.target.value; renderOverlays(); renderTimeline(); });
const rngTextSize = $('#rngTextSize'); undoableRange(rngTextSize);
rngTextSize.addEventListener('input', e => { const t=getSelectedText(); if(!t) return; t.size = +e.target.value; $('#valTextSize').textContent = t.size+'px'; renderOverlays(); });
const rngTextOpacity = $('#rngTextOpacity'); undoableRange(rngTextOpacity);
rngTextOpacity.addEventListener('input', e => { const t=getSelectedText(); if(!t) return; t.opacity = +e.target.value; $('#valTextOpacity').textContent = t.opacity+'%'; renderOverlays(); });
const rngTextRotate = $('#rngTextRotate'); undoableRange(rngTextRotate);
rngTextRotate.addEventListener('input', e => { const t=getSelectedText(); if(!t) return; t.rotate = +e.target.value; $('#valTextRotate').textContent = t.rotate+'°'; renderOverlays(); });
$$('#colorRow .swatch').forEach(sw => sw.addEventListener('click', () => {
  const t = getSelectedText(); if(!t) return;
  pushUndo();
  t.color = sw.dataset.color;
  $$('#colorRow .swatch').forEach(s=>s.classList.remove('active'));
  sw.classList.add('active');
  renderOverlays();
}));
$('#selFont').addEventListener('change', e => { const t=getSelectedText(); if(!t) return; pushUndo(); t.font = e.target.value; renderOverlays(); });
$('#selTextAnim').addEventListener('change', e => { const t=getSelectedText(); if(!t) return; pushUndo(); t.anim = e.target.value; renderOverlays(); });
$('#btnBold').addEventListener('click', () => { const t=getSelectedText(); if(!t) return; pushUndo(); t.bold=!t.bold; $('#btnBold').classList.toggle('active',t.bold); renderOverlays(); });
$('#btnItalic').addEventListener('click', () => { const t=getSelectedText(); if(!t) return; pushUndo(); t.italic=!t.italic; $('#btnItalic').classList.toggle('active',t.italic); renderOverlays(); });
$('#btnOutline').addEventListener('click', () => { const t=getSelectedText(); if(!t) return; pushUndo(); t.outline=!t.outline; $('#btnOutline').classList.toggle('active',t.outline); renderOverlays(); });
const rngTextStart = $('#rngTextStart'), rngTextEnd = $('#rngTextEnd');
undoableRange(rngTextStart); undoableRange(rngTextEnd);
rngTextStart.addEventListener('input', e => {
  const t = getSelectedText(); if(!t) return;
  t.startPct = Math.min(+e.target.value, t.endPct-1);
  e.target.value = t.startPct;
  renderTimeline(); renderOverlays();
});
rngTextEnd.addEventListener('input', e => {
  const t = getSelectedText(); if(!t) return;
  t.endPct = Math.max(+e.target.value, t.startPct+1);
  e.target.value = t.endPct;
  renderTimeline(); renderOverlays();
});
$('#btnDeleteText').addEventListener('click', () => {
  const t = getSelectedText(); if(!t) return;
  pushUndo();
  state.texts = state.texts.filter(x => x.id !== t.id);
  deselectAll(); renderLayers(); renderOverlays(); renderTimeline();
});

function textAnimState(t, curPct){
  const span = t.endPct - t.startPct;
  const localPct = span > 0 ? clamp((curPct - t.startPct)/span, 0, 1) : 1;
  const inWin = 0.15, outWin = 0.15;
  let opacity = 1, translateY = 0, scale = 1;
  if(t.anim === 'fade'){
    if(localPct < inWin) opacity = localPct/inWin;
    else if(localPct > 1-outWin) opacity = (1-localPct)/outWin;
  } else if(t.anim === 'slide'){
    if(localPct < inWin){ const p=localPct/inWin; opacity=p; translateY=(1-p)*30; }
    else if(localPct > 1-outWin){ const p=(1-localPct)/outWin; opacity=p; translateY=-(1-p)*30; }
  } else if(t.anim === 'pop'){
    if(localPct < inWin){ const p=localPct/inWin; opacity=p; scale=0.6+0.4*p; }
    else if(localPct > 1-outWin){ const p=(1-localPct)/outWin; opacity=p; scale=0.6+0.4*p; }
  }
  opacity *= (t.opacity!=null ? t.opacity/100 : 1);
  return { opacity, translateY, scale };
}

function renderOverlays(){
  els.overlayLayer.innerHTML = '';
  const rect = els.canvas.getBoundingClientRect();
  const scaleX = rect.width / CANVAS_W, scaleY = rect.height / CANVAS_H;
  const curPct = state.totalDuration ? (state.playhead/state.totalDuration)*100 : 0;

  state.texts.forEach(t => {
    if(curPct < t.startPct || curPct > t.endPct) return;
    const anim = textAnimState(t, curPct);
    const div = document.createElement('div');
    div.className = 'text-overlay' + (t.id === state.selectedTextId ? ' selected' : '');
    div.style.left = (t.x*100) + '%';
    div.style.top = (t.y*100) + '%';
    div.style.fontSize = (t.size*scaleY) + 'px';
    div.style.color = t.color;
    div.style.fontFamily = t.font;
    div.style.fontWeight = t.bold ? '700' : '500';
    div.style.fontStyle = t.italic ? 'italic' : 'normal';
    div.style.opacity = anim.opacity;
    div.style.webkitTextStroke = t.outline ? '1.5px rgba(0,0,0,0.85)' : '';
    div.style.transform = `translate(-50%,-50%) translateY(${anim.translateY}px) scale(${anim.scale}) rotate(${t.rotate||0}deg)`;
    div.textContent = t.text;
    div.addEventListener('mousedown', (e)=> startDragText(e, t));
    div.addEventListener('touchstart', (e)=> startDragText(e, t), {passive:false});
    div.addEventListener('click', (e)=>{ e.stopPropagation(); selectText(t.id); });
    els.overlayLayer.appendChild(div);
  });

  state.stickers.forEach(st => {
    const div = document.createElement('div');
    div.className = 'sticker-overlay' + (st.id === state.selectedStickerId ? ' selected' : '');
    div.style.left = (st.x*100) + '%';
    div.style.top = (st.y*100) + '%';
    div.style.transform = `translate(-50%,-50%) rotate(${st.rotate||0}deg)`;
    div.appendChild(stickerVisualEl(st, scaleY));
    const handle = document.createElement('div'); handle.className = 'resize-handle';
    div.appendChild(handle);
    div.addEventListener('mousedown', (e)=>{ if(e.target===handle) return; startDragSticker(e, st); });
    div.addEventListener('touchstart', (e)=>{ if(e.target===handle) return; startDragSticker(e, st); }, {passive:false});
    handle.addEventListener('mousedown', (e)=> startResizeSticker(e, st));
    handle.addEventListener('touchstart', (e)=> startResizeSticker(e, st), {passive:false});
    div.addEventListener('click', (e)=>{ e.stopPropagation(); selectSticker(st.id); });
    els.overlayLayer.appendChild(div);
  });
}
function stickerVisualEl(st, scaleY){
  const px = st.size*scaleY;
  if(st.type === 'emoji'){
    const span = document.createElement('span');
    span.style.fontSize = px+'px'; span.style.lineHeight = '1';
    span.textContent = st.emoji;
    return span;
  }
  const div = document.createElement('div');
  if(st.shapeType === 'rect'){ div.style.width=px+'px'; div.style.height=(px*0.62)+'px'; div.style.background=st.color; div.style.borderRadius='6px'; }
  else if(st.shapeType === 'circle'){ div.style.width=px+'px'; div.style.height=px+'px'; div.style.background=st.color; div.style.borderRadius='50%'; }
  else if(st.shapeType === 'line'){ div.style.width=px+'px'; div.style.height=Math.max(3,px*0.05)+'px'; div.style.background=st.color; }
  else if(st.shapeType === 'arrow'){ div.style.fontSize=px+'px'; div.style.color=st.color; div.textContent='➜'; }
  return div;
}
function startDragSticker(e, st){
  e.preventDefault(); e.stopPropagation();
  pushUndo();
  selectSticker(st.id);
  const move = (ev) => {
    const point = ev.touches ? ev.touches[0] : ev;
    const rect = els.canvas.getBoundingClientRect();
    st.x = clamp((point.clientX - rect.left)/rect.width, 0.02, 0.98);
    st.y = clamp((point.clientY - rect.top)/rect.height, 0.02, 0.98);
    renderOverlays();
  };
  const up = () => {
    window.removeEventListener('mousemove', move); window.removeEventListener('mouseup', up);
    window.removeEventListener('touchmove', move); window.removeEventListener('touchend', up);
    renderTimeline();
  };
  window.addEventListener('mousemove', move); window.addEventListener('mouseup', up);
  window.addEventListener('touchmove', move, {passive:false}); window.addEventListener('touchend', up);
}
function startResizeSticker(e, st){
  e.preventDefault(); e.stopPropagation();
  pushUndo();
  selectSticker(st.id);
  const rect = els.canvas.getBoundingClientRect();
  const move = (ev) => {
    const point = ev.touches ? ev.touches[0] : ev;
    const cx = rect.left + st.x*rect.width, cy = rect.top + st.y*rect.height;
    const dist = Math.hypot(point.clientX-cx, point.clientY-cy);
    st.size = clamp(Math.round((dist*2) / (rect.height/CANVAS_H)), 20, 400);
    updateStickerPanel(st);
    renderOverlays();
  };
  const up = () => {
    window.removeEventListener('mousemove', move); window.removeEventListener('mouseup', up);
    window.removeEventListener('touchmove', move); window.removeEventListener('touchend', up);
  };
  window.addEventListener('mousemove', move); window.addEventListener('mouseup', up);
  window.addEventListener('touchmove', move, {passive:false}); window.addEventListener('touchend', up);
}
function startDragText(e, t){
  e.preventDefault(); e.stopPropagation();
  pushUndo();
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

/* ---------------- stickers panel ---------------- */
const emojiGrid = $('#emojiGrid');
EMOJIS.forEach(em => {
  const btn = document.createElement('button');
  btn.textContent = em;
  btn.addEventListener('click', () => addSticker({ type:'emoji', emoji: em }));
  emojiGrid.appendChild(btn);
});
$$('.shape-chip').forEach(chip => {
  chip.addEventListener('click', () => addSticker({ type:'shape', shapeType: chip.dataset.shape }));
});
function addSticker(opts){
  if(!state.clips.length){ toast('Add a clip to the timeline first'); return; }
  pushUndo();
  const st = {
    id: uid(), type: opts.type, emoji: opts.emoji||'', shapeType: opts.shapeType||'rect',
    x:0.5, y:0.5, size:64, rotate:0, color:'#7c5cff',
  };
  state.stickers.push(st);
  renderLayers(); renderOverlays(); renderTimeline();
  selectSticker(st.id);
}
function updateStickerPanel(st){
  const has = !!st;
  $('#stickerEmpty').style.display = has ? 'none' : 'block';
  $('#stickerControls').style.display = has ? 'flex' : 'none';
  if(!has) return;
  $('#rngStickerSize').value = st.size; $('#valStickerSize').textContent = st.size+'px';
  $('#rngStickerRotate').value = st.rotate; $('#valStickerRotate').textContent = st.rotate+'°';
  $('#stickerColorField').style.display = st.type === 'shape' ? 'flex' : 'none';
  $$('#stickerColorRow .swatch').forEach(s => s.classList.toggle('active', s.dataset.color === st.color));
}
const rngStickerSize = $('#rngStickerSize'); undoableRange(rngStickerSize);
rngStickerSize.addEventListener('input', e => { const s=getSelectedSticker(); if(!s) return; s.size=+e.target.value; $('#valStickerSize').textContent=s.size+'px'; renderOverlays(); });
const rngStickerRotate = $('#rngStickerRotate'); undoableRange(rngStickerRotate);
rngStickerRotate.addEventListener('input', e => { const s=getSelectedSticker(); if(!s) return; s.rotate=+e.target.value; $('#valStickerRotate').textContent=s.rotate+'°'; renderOverlays(); });
$$('#stickerColorRow .swatch').forEach(sw => sw.addEventListener('click', () => {
  const s = getSelectedSticker(); if(!s) return;
  pushUndo();
  s.color = sw.dataset.color;
  $$('#stickerColorRow .swatch').forEach(x=>x.classList.remove('active'));
  sw.classList.add('active');
  renderOverlays();
}));
$('#btnDeleteSticker').addEventListener('click', () => {
  const s = getSelectedSticker(); if(!s) return;
  pushUndo();
  state.stickers = state.stickers.filter(x => x.id !== s.id);
  deselectAll(); renderLayers(); renderOverlays(); renderTimeline();
});

/* ---------------- layers panel ---------------- */
function renderLayers(){
  els.layersList.innerHTML = '';
  const items = [
    ...state.clips.map(c => ({ type:'clip', ref:c })),
    ...state.texts.map(t => ({ type:'text', ref:t })),
    ...state.stickers.map(s => ({ type:'sticker', ref:s })),
  ];
  els.layersEmpty.style.display = items.length ? 'none' : 'block';
  items.forEach(it => {
    const row = document.createElement('div');
    const selected = it.type==='clip' ? it.ref.id===state.selectedClipId
      : it.type==='text' ? it.ref.id===state.selectedTextId
      : it.ref.id===state.selectedStickerId;
    row.style.cssText = `display:flex;align-items:center;gap:8px;padding:8px 10px;border-radius:8px;cursor:pointer;border:1px solid ${selected?'var(--teal)':'var(--line)'};background:var(--ink-800);font-size:12.5px;`;
    const dot = it.type==='clip' ? 'var(--violet)' : it.type==='text' ? 'var(--teal)' : 'var(--coral)';
    const label = it.type==='clip' ? it.ref.name
      : it.type==='text' ? `"${it.ref.text.slice(0,18)}"`
      : (it.ref.type==='emoji' ? it.ref.emoji : it.ref.shapeType);
    row.innerHTML = `<span style="width:8px;height:8px;border-radius:2px;background:${dot};flex:none;"></span><span style="overflow:hidden;text-overflow:ellipsis;white-space:nowrap;">${label}</span>`;
    row.addEventListener('click', () => it.type==='clip' ? selectClip(it.ref.id) : it.type==='text' ? selectText(it.ref.id) : selectSticker(it.ref.id));
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
    label.textContent = c.name + (c.speed!==1 ? ` · ${c.speed.toFixed(2)}×` : '') + (c.transitionType!=='none' ? ` · ${c.transitionType}`:'');
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

  // sticker lane (full width, decorative markers)
  els.laneStickers.innerHTML = '';
  els.laneStickers.style.width = totalW + 'px';
  state.stickers.forEach((s,i) => {
    const el = document.createElement('div');
    el.className = 'tl-clip sticker-clip' + (s.id===state.selectedStickerId ? ' selected':'');
    el.style.left = (i*90) + 'px';
    el.style.width = '80px';
    const label = document.createElement('div'); label.className='clip-label';
    label.textContent = s.type==='emoji' ? s.emoji : ('◆ '+s.shapeType);
    el.appendChild(label);
    el.addEventListener('click', (e)=>{ e.stopPropagation(); selectSticker(s.id); });
    els.laneStickers.appendChild(el);
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

/* ---- snapping helper ---- */
function snapValue(val, candidates, thresholdSec){
  if(!els.chkSnap.checked) return val;
  let best = val, bestDist = thresholdSec;
  candidates.forEach(cand => {
    const d = Math.abs(cand - val);
    if(d < bestDist){ bestDist = d; best = cand; }
  });
  return best;
}
function clipBoundaryCandidates(excludeId){
  const arr = [0];
  state.clips.forEach(c => { if(c.id!==excludeId){ arr.push(c.seqStart); arr.push(c.seqStart+c.seqDur); } });
  arr.push(state.playhead);
  return arr;
}

/* ---- drag clip to reorder ---- */
function startDragClip(e, clip){
  e.preventDefault();
  pushUndo();
  selectClip(clip.id);
  const startX = e.clientX;
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
  pushUndo();
  selectClip(clip.id);
  const pps = pxPerSec();
  const startX = e.clientX;
  const origIn = clip.trimIn, origOut = clip.trimOut;
  const move = (ev) => {
    const dx = (ev.clientX - startX) / pps;
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
els.btnDuplicateClip.addEventListener('click', duplicateSelectedClip);
document.addEventListener('keydown', (e) => {
  const tag = (e.target.tagName||'').toLowerCase();
  if(tag==='input' || tag==='textarea') return;
  if(e.code === 'Space'){ e.preventDefault(); togglePlay(); }
  if(e.key.toLowerCase()==='s' && !e.ctrlKey && !e.metaKey){ splitAtPlayhead(); }
  if(e.key === 'Delete' || e.key === 'Backspace'){ deleteSelected(); }
  if((e.ctrlKey||e.metaKey) && e.key.toLowerCase()==='z' && !e.shiftKey){ e.preventDefault(); undo(); }
  if((e.ctrlKey||e.metaKey) && (e.key.toLowerCase()==='y' || (e.key.toLowerCase()==='z' && e.shiftKey))){ e.preventDefault(); redo(); }
  if((e.ctrlKey||e.metaKey) && e.key.toLowerCase()==='d'){ e.preventDefault(); duplicateSelectedClip(); }
  if(e.key === 'ArrowLeft'){ seekTo(state.playhead - 1/30); }
  if(e.key === 'ArrowRight'){ seekTo(state.playhead + 1/30); }
  if(e.key === '='){ state.zoomPxPerSec = clamp(state.zoomPxPerSec+10,20,200); els.rngZoom.value=state.zoomPxPerSec; renderTimeline(); }
  if(e.key === '-'){ state.zoomPxPerSec = clamp(state.zoomPxPerSec-10,20,200); els.rngZoom.value=state.zoomPxPerSec; renderTimeline(); }
});
function splitAtPlayhead(){
  const c = getActiveClip(state.playhead);
  if(!c || (c.kind!=='video' && c.kind!=='image')) return;
  const local = localTimeFor(c, state.playhead);
  if(local - c.trimIn < 0.15 || c.trimOut - local < 0.15) { toast('Move the playhead further into the clip to split'); return; }
  pushUndo();
  const idx = state.clips.indexOf(c);
  const clone = { ...c, id: uid(), trimIn: local, filters:{...c.filters}, chroma:{...c.chroma}, transitionType:'none' };
  clipPool.set(clone.id, clone);
  c.trimOut = local;
  state.clips.splice(idx+1, 0, clone);
  recalcTimeline(); renderTimeline(); renderLayers(); renderFrame();
  toast('Split clip');
}
function duplicateSelectedClip(){
  const c = getSelectedClip(); if(!c) return;
  pushUndo();
  const clone = { ...c, id: uid(), filters:{...c.filters}, chroma:{...c.chroma} };
  clipPool.set(clone.id, clone);
  const idx = state.clips.indexOf(c);
  state.clips.splice(idx+1, 0, clone);
  recalcTimeline(); renderTimeline(); renderLayers(); renderFrame();
  selectClip(clone.id);
  toast('Clip duplicated');
}
els.btnDeleteClip.addEventListener('click', deleteSelected);
function deleteSelected(){
  if(state.selectedClipId){
    pushUndo();
    state.clips = state.clips.filter(c => c.id !== state.selectedClipId);
    state.selectedClipId = null;
    recalcTimeline(); renderTimeline(); renderLayers(); showStage(); renderFrame();
  } else if(state.selectedTextId){
    pushUndo();
    state.texts = state.texts.filter(t => t.id !== state.selectedTextId);
    state.selectedTextId = null;
    renderTimeline(); renderLayers(); renderOverlays();
  } else if(state.selectedStickerId){
    pushUndo();
    state.stickers = state.stickers.filter(s => s.id !== state.selectedStickerId);
    state.selectedStickerId = null;
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
      updateMusicVolume();
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
  updateMusicVolume();
  rafId = requestAnimationFrame(playLoop);
}

/* ---------------- rendering a frame ---------------- */
const bufferCache = new Map();
function getBuffer(key, w, h){
  let b = bufferCache.get(key);
  if(!b || b.width!==w || b.height!==h){ b = document.createElement('canvas'); b.width=w; b.height=h; bufferCache.set(key,b); }
  return b;
}
let noiseTile = null;
function getNoiseTile(){
  if(noiseTile) return noiseTile;
  const c = document.createElement('canvas'); c.width=128; c.height=128;
  const ictx = c.getContext('2d');
  const img = ictx.createImageData(128,128);
  for(let i=0;i<img.data.length;i+=4){
    const v = Math.floor(Math.random()*255);
    img.data[i]=v; img.data[i+1]=v; img.data[i+2]=v; img.data[i+3]=255;
  }
  ictx.putImageData(img,0,0);
  noiseTile = c;
  return c;
}
function filterString(f){
  const sepia = f.temp > 0 ? clamp(f.temp/100, 0, 0.4) : 0;
  const hueFromTemp = f.temp < 0 ? clamp(-f.temp*0.9, 0, 40) : 0;
  const hue = hueFromTemp + (f.hue||0);
  const brightness = f.brightness * (1 + (f.exposure||0)/100);
  const contrastBoost = f.sharpen ? (1 + (f.sharpen/100)*0.5) : 1;
  const saturateBoost = f.sharpen ? (1 + (f.sharpen/100)*0.15) : 1;
  const blur = f.blur ? ` blur(${f.blur}px)` : '';
  return `brightness(${brightness}%) contrast(${f.contrast*contrastBoost}%) saturate(${f.saturation*saturateBoost}%) sepia(${sepia}) hue-rotate(${hue}deg)${blur}`;
}
function drawCoverInto(targetCtx, source, sw, sh, tw, th){
  const scale = Math.max(tw/sw, th/sh);
  const dw = sw*scale, dh = sh*scale;
  targetCtx.drawImage(source, (tw-dw)/2, (th-dh)/2, dw, dh);
}
function drawVignetteInto(targetCtx, tw, th, amount){
  if(!amount) return;
  const g = targetCtx.createRadialGradient(tw/2, th/2, th*0.35, tw/2, th/2, th*0.85);
  g.addColorStop(0, 'rgba(0,0,0,0)');
  g.addColorStop(1, `rgba(0,0,0,${(amount/100)*0.7})`);
  targetCtx.save();
  targetCtx.fillStyle = g;
  targetCtx.fillRect(0,0,tw,th);
  targetCtx.restore();
}
function drawGrainInto(targetCtx, tw, th, amount){
  if(!amount) return;
  targetCtx.save();
  targetCtx.globalAlpha = (amount/100) * 0.5;
  targetCtx.globalCompositeOperation = 'overlay';
  const pattern = targetCtx.createPattern(getNoiseTile(), 'repeat');
  targetCtx.fillStyle = pattern;
  targetCtx.fillRect(0,0,tw,th);
  targetCtx.restore();
}
function applyChromaKeyTo(targetCtx, tw, th, chroma){
  if(!chroma || !chroma.enabled) return;
  const [kr,kg,kb] = hexToRgb(chroma.color);
  const sim = clamp(chroma.similarity,1,100)/100;
  const smooth = Math.max(0.01, chroma.smoothness/100);
  let img;
  try{ img = targetCtx.getImageData(0,0,tw,th); }catch(_e){ return; }
  const d = img.data;
  for(let i=0;i<d.length;i+=4){
    if(d[i+3]===0) continue;
    const r=d[i],g=d[i+1],b=d[i+2];
    const dist = Math.sqrt((r-kr)*(r-kr)+(g-kg)*(g-kg)+(b-kb)*(b-kb))/441.673;
    if(dist < sim){ d[i+3]=0; }
    else if(dist < sim+smooth){ d[i+3] = Math.round(d[i+3]*((dist-sim)/smooth)); }
  }
  targetCtx.putImageData(img,0,0);
}
// Draws one clip's fully-graded frame into an arbitrary (already-cleared) context.
function drawClipToCtx(targetCtx, c, localTime, tw, th, opts={}){
  targetCtx.clearRect(0,0,tw,th);
  targetCtx.save();
  targetCtx.filter = filterString(c.filters);
  if(c.kind === 'video'){
    if(!opts.liveVideo && Math.abs(c.el.currentTime - localTime) > 0.06 && c.el.readyState >= 2){
      try{ c.el.currentTime = localTime; }catch(_e){}
    }
    try{ drawCoverInto(targetCtx, c.el, c.el.videoWidth||tw, c.el.videoHeight||th, tw, th); }catch(_e){}
  } else {
    drawCoverInto(targetCtx, c.el, c.el.naturalWidth||tw, c.el.naturalHeight||th, tw, th);
  }
  targetCtx.restore();
  applyChromaKeyTo(targetCtx, tw, th, c.chroma);
  drawGrainInto(targetCtx, tw, th, c.filters.grain);
  drawVignetteInto(targetCtx, tw, th, c.filters.vignette);
}
function blendTransition(targetCtx, tw, th, fromCanvas, toCanvas, type, progress){
  targetCtx.save();
  switch(type){
    case 'fade':
      targetCtx.globalAlpha = 1; targetCtx.drawImage(fromCanvas,0,0,tw,th);
      targetCtx.globalAlpha = progress; targetCtx.drawImage(toCanvas,0,0,tw,th);
      break;
    case 'slide':
      targetCtx.globalAlpha = 1;
      targetCtx.drawImage(fromCanvas, -progress*tw, 0, tw, th);
      targetCtx.drawImage(toCanvas, tw - progress*tw, 0, tw, th);
      break;
    case 'wipe':
      targetCtx.globalAlpha = 1;
      targetCtx.drawImage(fromCanvas,0,0,tw,th);
      targetCtx.save();
      targetCtx.beginPath(); targetCtx.rect(0,0, tw*progress, th); targetCtx.clip();
      targetCtx.drawImage(toCanvas,0,0,tw,th);
      targetCtx.restore();
      break;
    case 'zoom': {
      targetCtx.globalAlpha = 1 - progress; targetCtx.drawImage(fromCanvas,0,0,tw,th);
      targetCtx.globalAlpha = progress;
      const scale = 1.15 - 0.15*progress;
      const dw = tw*scale, dh = th*scale;
      targetCtx.drawImage(toCanvas, (tw-dw)/2, (th-dh)/2, dw, dh);
      break;
    }
    default:
      targetCtx.globalAlpha = 1; targetCtx.drawImage(toCanvas,0,0,tw,th);
  }
  targetCtx.restore();
}
// Full sequence compositor used by both the live preview and the exporter.
function compositeFrame(targetCtx, tw, th, seqTime, opts={}){
  targetCtx.fillStyle = '#000';
  targetCtx.fillRect(0,0,tw,th);
  if(!state.clips.length) return;
  const idx = state.clips.findIndex(c => seqTime >= c.seqStart && seqTime < c.seqStart+c.seqDur);
  const active = idx >= 0 ? state.clips[idx] : (seqTime >= state.totalDuration ? state.clips[state.clips.length-1] : null);
  if(!active) return;
  const activeIdx = state.clips.indexOf(active);
  const prev = activeIdx > 0 ? state.clips[activeIdx-1] : null;
  const tType = active.transitionType || 'none';
  const tDur = active.transitionDur || 0;
  const localActive = localTimeFor(active, seqTime);
  const bufA = getBuffer('a', tw, th), bufB = getBuffer('b', tw, th);
  if(prev && tType !== 'none' && tDur > 0 && (seqTime - active.seqStart) < tDur && !opts.frozenPrev){
    const progress = clamp((seqTime - active.seqStart)/tDur, 0, 1);
    drawClipToCtx(bufA.getContext('2d'), prev, prev.trimOut - 0.01, tw, th);
    drawClipToCtx(bufB.getContext('2d'), active, localActive, tw, th, opts);
    blendTransition(targetCtx, tw, th, bufA, bufB, tType, progress);
  } else if(opts.frozenPrev && tType !== 'none' && tDur > 0 && opts.elapsedInClip < tDur){
    const progress = clamp(opts.elapsedInClip/tDur, 0, 1);
    drawClipToCtx(bufB.getContext('2d'), active, localActive, tw, th, opts);
    blendTransition(targetCtx, tw, th, opts.frozenPrev, bufB, tType, progress);
  } else {
    drawClipToCtx(bufB.getContext('2d'), active, localActive, tw, th, opts);
    targetCtx.drawImage(bufB, 0, 0, tw, th);
  }
}
function renderFrame(){
  compositeFrame(ctx, CANVAS_W, CANVAS_H, state.playhead);
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
function populateResOptions(){
  const list = RES_PRESETS[state.aspect];
  els.selRes.innerHTML = list.map(([w,h,label]) => `<option value="${w}x${h}">${w} × ${h} (${label})</option>`).join('');
}
els.btnExport.addEventListener('click', () => {
  if(state.clips.length===0){ toast('Add a clip before exporting'); return; }
  populateResOptions();
  els.exportModal.classList.add('show');
  els.exportSetup.style.display = 'block';
  els.exportProgress.style.display = 'none';
  els.btnStartExport.style.display = 'inline-flex';
});
els.btnCancelExport.addEventListener('click', () => els.exportModal.classList.remove('show'));

els.btnStartExport.addEventListener('click', runExport);

function drawExportOverlays(exCtx, w, h, seqTime){
  const curPct = state.totalDuration ? (seqTime/state.totalDuration)*100 : 0;
  const scaleY = h/CANVAS_H, scaleX = w/CANVAS_W;
  state.texts.forEach(t => {
    if(curPct < t.startPct || curPct > t.endPct) return;
    const anim = textAnimState(t, curPct);
    if(anim.opacity <= 0.01) return;
    exCtx.save();
    exCtx.globalAlpha = anim.opacity;
    const px = t.x*w, py = t.y*h + anim.translateY*scaleY;
    exCtx.translate(px, py);
    exCtx.rotate((t.rotate||0) * Math.PI/180);
    exCtx.scale(anim.scale, anim.scale);
    const weight = t.bold ? '700' : '500';
    const style = t.italic ? 'italic' : 'normal';
    exCtx.font = `${style} ${weight} ${t.size*scaleY}px ${t.font}`;
    exCtx.fillStyle = t.color;
    exCtx.textAlign = 'center';
    exCtx.textBaseline = 'middle';
    if(t.outline){ exCtx.lineWidth = 3; exCtx.strokeStyle = 'rgba(0,0,0,0.85)'; }
    exCtx.shadowColor = 'rgba(0,0,0,0.6)';
    exCtx.shadowBlur = 10;
    const lines = t.text.split('\n');
    const lh = t.size*scaleY*1.2;
    lines.forEach((line,i)=>{
      const ly = (i-(lines.length-1)/2)*lh;
      if(t.outline) exCtx.strokeText(line, 0, ly);
      exCtx.fillText(line, 0, ly);
    });
    exCtx.restore();
  });
  state.stickers.forEach(st => {
    exCtx.save();
    exCtx.translate(st.x*w, st.y*h);
    exCtx.rotate((st.rotate||0) * Math.PI/180);
    const px = st.size*scaleY;
    if(st.type === 'emoji'){
      exCtx.font = `${px}px sans-serif`;
      exCtx.textAlign = 'center'; exCtx.textBaseline = 'middle';
      exCtx.fillText(st.emoji, 0, 0);
    } else if(st.shapeType === 'rect'){
      exCtx.fillStyle = st.color;
      exCtx.fillRect(-px/2, -px*0.31, px, px*0.62);
    } else if(st.shapeType === 'circle'){
      exCtx.fillStyle = st.color;
      exCtx.beginPath(); exCtx.arc(0,0,px/2,0,Math.PI*2); exCtx.fill();
    } else if(st.shapeType === 'line'){
      exCtx.strokeStyle = st.color; exCtx.lineWidth = Math.max(2,px*0.05);
      exCtx.beginPath(); exCtx.moveTo(-px/2,0); exCtx.lineTo(px/2,0); exCtx.stroke();
    } else if(st.shapeType === 'arrow'){
      exCtx.font = `${px}px sans-serif`; exCtx.fillStyle = st.color;
      exCtx.textAlign='center'; exCtx.textBaseline='middle';
      exCtx.fillText('➜', 0, 0);
    }
    exCtx.restore();
  });
}

async function runExport(){
  pausePlayback();
  const [w,h] = els.selRes.value.split('x').map(Number);
  const fps = +els.selFps.value;
  const quality = +els.selQuality.value; // Mbps
  els.exportSetup.style.display = 'none';
  els.exportProgress.style.display = 'block';
  els.btnStartExport.style.display = 'none';

  const exportCanvas = document.createElement('canvas');
  exportCanvas.width = w; exportCanvas.height = h;
  const ex = exportCanvas.getContext('2d');

  let audioCtx, dest, mixed = false, musicGain = null;
  try{
    audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    dest = audioCtx.createMediaStreamDestination();
    if(state.music){
      const src = audioCtx.createMediaElementSource(state.music.el);
      musicGain = audioCtx.createGain();
      const baseVol = state.music.volume/100;
      const fadeSec = state.music.fade || 0;
      const t0 = audioCtx.currentTime;
      const total = Math.max(0.01, state.totalDuration);
      if(fadeSec > 0){
        musicGain.gain.setValueAtTime(0, t0);
        musicGain.gain.linearRampToValueAtTime(baseVol, t0 + Math.min(fadeSec, total/2));
        musicGain.gain.setValueAtTime(baseVol, t0 + Math.max(fadeSec, total - fadeSec));
        musicGain.gain.linearRampToValueAtTime(0, t0 + total);
      } else {
        musicGain.gain.setValueAtTime(baseVol, t0);
      }
      src.connect(musicGain).connect(dest);
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

  const canvasStream = exportCanvas.captureStream(fps);
  const tracks = [...canvasStream.getVideoTracks()];
  if(mixed && dest) tracks.push(...dest.stream.getAudioTracks());
  const finalStream = new MediaStream(tracks);

  const wantMp4 = els.selFormat.value === 'mp4';
  let mimeType = 'video/webm;codecs=vp9,opus';
  if(wantMp4 && MediaRecorder.isTypeSupported('video/mp4;codecs=avc1,mp4a.40.2')){
    mimeType = 'video/mp4;codecs=avc1,mp4a.40.2';
  } else {
    if(wantMp4) toast('MP4 not supported in this browser — exporting WebM instead');
    if(!MediaRecorder.isTypeSupported(mimeType)) mimeType = 'video/webm;codecs=vp8,opus';
    if(!MediaRecorder.isTypeSupported(mimeType)) mimeType = 'video/webm';
  }
  const ext = mimeType.startsWith('video/mp4') ? 'mp4' : 'webm';

  const recorder = new MediaRecorder(finalStream, { mimeType, videoBitsPerSecond: quality * 1_000_000 });
  const chunks = [];
  recorder.ondataavailable = e => { if(e.data.size>0) chunks.push(e.data); };

  const finished = new Promise(resolve => { recorder.onstop = resolve; });
  recorder.start();

  if(state.music){ try{ state.music.el.currentTime = 0; await state.music.el.play(); }catch(_e){} }

  function exDrawVignette(amount){ drawVignetteInto(ex, w, h, amount); }
  function exFilterString(f){ return filterString(f); }
  function exDrawCover(source, sw, sh2){ drawCoverInto(ex, source, sw, sh2, w, h); }

  let frozenPrev = null;

  for(let i=0;i<state.clips.length;i++){
    const c = state.clips[i];
    els.progressLabel.textContent = `Rendering clip ${i+1} of ${state.clips.length}…`;
    const tType = c.transitionType || 'none';
    const tDur = c.transitionDur || 0;
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
            const snap = document.createElement('canvas'); snap.width=w; snap.height=h;
            snap.getContext('2d').drawImage(exportCanvas,0,0);
            frozenPrev = snap;
            resolve();
            return;
          }
          const seqTime = c.seqStart + (c.el.currentTime - c.trimIn)/c.speed;
          const elapsedInClip = seqTime - c.seqStart;
          if(i>0 && frozenPrev && tType!=='none' && tDur>0 && elapsedInClip < tDur){
            const bufB = getBuffer('exb', w, h);
            drawClipToCtx(bufB.getContext('2d'), c, c.el.currentTime, w, h, {liveVideo:true});
            blendTransition(ex, w, h, frozenPrev, bufB, tType, clamp(elapsedInClip/tDur,0,1));
          } else {
            drawClipToCtx(ex, c, c.el.currentTime, w, h, {liveVideo:true});
          }
          drawExportOverlays(ex, w, h, seqTime);
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
          if(elapsed >= dur){
            const snap = document.createElement('canvas'); snap.width=w; snap.height=h;
            snap.getContext('2d').drawImage(exportCanvas,0,0);
            frozenPrev = snap;
            resolve();
            return;
          }
          const seqTime = c.seqStart + elapsed;
          if(i>0 && frozenPrev && tType!=='none' && tDur>0 && elapsed < tDur){
            const bufB = getBuffer('exb', w, h);
            drawClipToCtx(bufB.getContext('2d'), c, c.trimIn + elapsed, w, h);
            blendTransition(ex, w, h, frozenPrev, bufB, tType, clamp(elapsed/tDur,0,1));
          } else {
            drawClipToCtx(ex, c, c.trimIn + elapsed, w, h);
          }
          drawExportOverlays(ex, w, h, seqTime);
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

  const blob = new Blob(chunks, { type: mimeType.split(';')[0] });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = (els.projName.value || 'vull_export') + '.' + ext;
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
applyAspect(state.aspect);
recalcTimeline();
renderTimeline();
renderLayers();
showStage();
playIcon(false);
updateUndoRedoButtons();

})();
