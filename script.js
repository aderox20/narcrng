(() => {
'use strict';

/* ---------- Format ----------
   Fragment = Base64URL( header(6 bytes) + packed samples )
   header: [version=1, durHi, durLo (duration in 1/10 s, uint16), bits, countHi, countLo]
   samples: `count` values of `bits` bits, MSB first, zero padded.
   Each value q = round(sqrt(peak/maxPeak) * (2^bits-1))  (sqrt companding)
   Optional title: appended to fragment as "~" + encodeURIComponent(title)
*/
const VERSION = 1;
const URL_WARN_LEN = 2000;

const $ = id => document.getElementById(id);
const fmt = s => `${Math.floor(s / 60)}:${String(Math.floor(s % 60)).padStart(2, '0')}`;

/* ---------- Base64URL ---------- */
function b64uEncode(bytes) {
  let s = '';
  for (let i = 0; i < bytes.length; i++) s += String.fromCharCode(bytes[i]);
  return btoa(s).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
}
function b64uDecode(str) {
  str = str.replace(/-/g, '+').replace(/_/g, '/');
  while (str.length % 4) str += '=';
  const bin = atob(str);
  const out = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
  return out;
}

/* ---------- Pack / unpack ---------- */
function pack(q, bits, duration) {
  const n = q.length;
  const body = new Uint8Array(Math.ceil(n * bits / 8));
  let bitPos = 0;
  for (let i = 0; i < n; i++) {
    for (let b = bits - 1; b >= 0; b--) {
      if ((q[i] >> b) & 1) body[bitPos >> 3] |= 0x80 >> (bitPos & 7);
      bitPos++;
    }
  }
  const d = Math.min(65535, Math.round(duration * 10));
  const out = new Uint8Array(6 + body.length);
  out.set([VERSION, d >> 8, d & 255, bits, n >> 8, n & 255]);
  out.set(body, 6);
  return out;
}
function unpack(bytes) {
  if (bytes.length < 7 || bytes[0] !== VERSION) throw new Error('Unsupported or corrupt data');
  const duration = ((bytes[1] << 8) | bytes[2]) / 10;
  const bits = bytes[3];
  const n = (bytes[4] << 8) | bytes[5];
  if (bits < 1 || bits > 8 || n < 1 || bytes.length < 6 + Math.ceil(n * bits / 8)) throw new Error('Corrupt data');
  const q = new Uint8Array(n);
  let bitPos = 0;
  for (let i = 0; i < n; i++) {
    let v = 0;
    for (let b = 0; b < bits; b++) {
      const byte = bytes[6 + (bitPos >> 3)];
      v = (v << 1) | ((byte >> (7 - (bitPos & 7))) & 1);
      bitPos++;
    }
    q[i] = v;
  }
  return { duration, bits, q };
}

/* ---------- Analysis ---------- */
function analyze(audioBuffer, nBars, bits) {
  const ch = audioBuffer.numberOfChannels;
  const len = audioBuffer.length;
  const data = [];
  for (let c = 0; c < ch; c++) data.push(audioBuffer.getChannelData(c));
  const peaks = new Float32Array(nBars);
  let max = 0;
  for (let i = 0; i < nBars; i++) {
    const a = Math.floor(i * len / nBars);
    const b = Math.max(Math.floor((i + 1) * len / nBars), a + 1);
    let p = 0;
    for (let j = a; j < b; j++) {
      let s = 0;
      for (let c = 0; c < ch; c++) s += data[c][j];
      s = Math.abs(s / ch);
      if (s > p) p = s;
    }
    peaks[i] = p;
    if (p > max) max = p;
  }
  const L = (1 << bits) - 1;
  const q = new Uint8Array(nBars);
  for (let i = 0; i < nBars; i++) q[i] = Math.round(Math.sqrt(max ? peaks[i] / max : 0) * L);
  return { q, duration: audioBuffer.duration };
}

/* ---------- SVG ---------- */
const SVG_NS = 'http://www.w3.org/2000/svg';
function buildSVG(q, bits, { standalone = false } = {}) {
  const n = q.length, L = (1 << bits) - 1, H = 100, mid = H / 2;
  const bw = 0.62; // bar width as fraction of slot
  let d = '';
  for (let i = 0; i < n; i++) {
    const v = q[i] / L;
    const amp = v * v; // undo sqrt companding
    const h = Math.max(1.2, amp * (H - 6));
    const x = (i + (1 - bw) / 2).toFixed(2);
    d += `M${x} ${(mid - h / 2).toFixed(2)}h${bw}v${h.toFixed(2)}h-${bw}z`;
  }
  const w = standalone ? ` width="${n * 4}" height="400"` : '';
  const bg = standalone ? `<rect width="${n}" height="${H}" fill="#0e1118"/>` : '';
  return `<svg xmlns="${SVG_NS}" viewBox="0 0 ${n} ${H}" preserveAspectRatio="none"${w}>` +
    `<defs><linearGradient id="g" x1="0" x2="1"><stop offset="0" stop-color="#7c5cff"/><stop offset="1" stop-color="#22d3ee"/></linearGradient>` +
    `<clipPath id="played"><rect id="clipRect" x="0" y="0" width="${standalone ? n : 0}" height="${H}"/></clipPath></defs>` +
    bg +
    `<path d="${d}" fill="${standalone ? 'url(#g)' : '#3a4258'}"/>` +
    (standalone ? '' : `<path d="${d}" fill="url(#g)" clip-path="url(#played)"/>`) +
    `</svg>`;
}

/* ---------- State ---------- */
let current = null;      // { q, bits, duration, title }
let audioEl = null;
let rafId = 0;

/* ---------- Location helpers ----------
   Shared data is stored in the URL hash so GitHub Pages never needs to route the
   encoded data through a 404 page. Hash URLs also work locally and on project pages. */
const onPages = /\.github\.io$/.test(location.hostname);
function repoRoot() {
  if (!onPages) return location.origin + location.pathname.replace(/[^/]*$/, '');
  const first = location.pathname.split('/')[1] || '';
  return location.origin + '/' + (first ? first + '/' : '');
}
function readData() {
  if (location.hash.length > 1) return location.hash.slice(1);
  if (!onPages) return '';
  const parts = location.pathname.split('/').filter(Boolean);
  return parts.length > 1 ? parts.slice(1).join('') : '';
}

/* ---------- Viewer ---------- */
function showWaveform(wf) {
  current = wf;
  $('viewer').hidden = false;
  $('empty').hidden = true;
  $('waveHost').innerHTML = buildSVG(wf.q, wf.bits);
  $('metaTitle').textContent = wf.title || 'Shared waveform';
  $('metaInfo').textContent = `${fmt(wf.duration)} · ${wf.q.length} bars · ${wf.bits}-bit`;
  $('tot').textContent = fmt(wf.duration);
  $('cur').textContent = '0:00';
  document.title = wf.title ? `${wf.title} – Waveform` : 'Waveform Share';
  setProgress(0);
}

function setProgress(frac) {
  frac = Math.max(0, Math.min(1, frac || 0));
  const rect = $('clipRect');
  if (rect && current) rect.setAttribute('width', frac * current.q.length);
  const ph = $('playhead');
  ph.style.display = audioEl ? 'block' : 'none';
  ph.style.left = `calc(${frac * 100}% - 1px)`;
}

function loadFromHash() {
  const raw = readData();
  if (!raw) { $('viewer').hidden = true; $('empty').hidden = false; return; }
  try {
    let [data, t] = raw.split('~');
    const dec = unpack(b64uDecode(data));
    showWaveform({ ...dec, title: t ? decodeURIComponent(t) : '' });
  } catch (e) {
    $('viewer').hidden = true;
    $('empty').hidden = false;
    $('empty').firstElementChild.textContent = 'Could not read the waveform in this URL (' + e.message + ').';
  }
}

/* ---------- Playback (local file only) ---------- */
function attachAudio(file) {
  if (audioEl) { audioEl.pause(); URL.revokeObjectURL(audioEl.src); }
  audioEl = new Audio(URL.createObjectURL(file));
  audioEl.preload = 'metadata';
  audioEl.addEventListener('ended', () => { updatePlayIcon(); setProgress(1); });
  audioEl.addEventListener('pause', updatePlayIcon);
  audioEl.addEventListener('play', () => { updatePlayIcon(); tick(); });
  $('playBtn').disabled = false;
  $('playHint').textContent = 'Playing from your local file. It is not uploaded anywhere.';
  $('loadAudioLbl').textContent = 'Change audio';
  setProgress(0);
}
function updatePlayIcon() {
  const playing = audioEl && !audioEl.paused && !audioEl.ended;
  $('playIcon').innerHTML = playing
    ? '<path d="M6 5h4v14H6zM14 5h4v14h-4z" fill="currentColor"/>'
    : '<path d="M8 5v14l11-7z" fill="currentColor"/>';
  $('playBtn').setAttribute('aria-label', playing ? 'Pause' : 'Play');
}
function tick() {
  cancelAnimationFrame(rafId);
  if (!audioEl) return;
  const dur = audioEl.duration || (current && current.duration) || 1;
  setProgress(audioEl.currentTime / dur);
  $('cur').textContent = fmt(audioEl.currentTime);
  if (!audioEl.paused) rafId = requestAnimationFrame(tick);
}
function togglePlay() {
  if (!audioEl) return;
  if (audioEl.paused) audioEl.play().catch(() => {}); else audioEl.pause();
}
const STAGE_2_DATA = 'AQNkBQHMBrWta1rWta1rWta1reta1rWtb1rWta1rWta1rWta1nOc51rWta1rWta1rWud9znPd77nOc1rWta1rWta1nOc5znOc5znOc5zrWta1rWtb3rWt61veta1rWtaznOc51rWda1rnO873ve95z3ec7znO87zv-85zne853vOZznOc5znOd73ve971rWta1rWta1rWta1rWta1ve973Oc5znOc851rWta1rWta1e973vfOta1rWta1rWta1rF73vfGL3ve98Yve973vjF73ve-MXve974xi9--73vO97zmc5znOc5znOc5znOc5zmbGMYxjGMYxjGVrW1a1rW1a2rWtbVrWta1rzvO87zvO61rWtaz3ve853Wta1rWta1rWta1vc5znOcw~d.o';

function checkStage2(e) {
  if (!current || readData() !== STAGE_2_DATA) return;
  const r = $('waveWrap').getBoundingClientRect();
  const frac = Math.max(0, Math.min(1, (e.clientX - r.left) / r.width));
  const index = Math.floor(frac * current.q.length);
  // Hidden ARG trigger: one specific waveform segment reveals Stage 2.
  if (index >= 0 && index < current.q.length) {
    alert('STAGE 2 FOUND — TEST');
    $('metaTitle').textContent = 'STAGE 2 FOUND — TEST';
    $('metaInfo').textContent = 'You found something hidden in the waveform.';
  }
}

function seekFromEvent(e) {
  checkStage2(e);
  if (!audioEl) return;
  const r = $('waveWrap').getBoundingClientRect();
  const frac = Math.max(0, Math.min(1, (e.clientX - r.left) / r.width));
  const dur = audioEl.duration || current.duration;
  audioEl.currentTime = frac * dur;
  tick();
}

/* ---------- Generator ---------- */
let decodedBuffer = null;
let actx = null;

async function handleGenFile(file) {
  if (!file) return;
  $('drop').querySelector('strong').textContent = 'Decoding ' + file.name + '…';
  try {
    actx = actx || new (window.AudioContext || window.webkitAudioContext)();
    const buf = await file.arrayBuffer();
    decodedBuffer = await actx.decodeAudioData(buf);
    $('drop').querySelector('strong').textContent = file.name;
    if (!$('title').value) $('title').value = file.name.replace(/\.[^.]+$/, '').slice(0, 40);
    regenerate();
    attachAudio(file); // lets you play it locally alongside the preview
  } catch (e) {
    $('drop').querySelector('strong').textContent = 'Could not decode that file';
    console.error(e);
  }
}

function regenerate() {
  if (!decodedBuffer) return;
  const n = +$('bars').value, bits = +$('bits').value;
  $('barsOut').textContent = n;
  const { q, duration } = analyze(decodedBuffer, n, bits);
  const title = $('title').value.trim();
  const frag = b64uEncode(pack(q, bits, duration)) + (title ? '~' + encodeURIComponent(title) : '');
  const url = `${location.href.split('#')[0]}#${frag}`;

  $('result').hidden = false;
  $('urlBox').value = '/#' + frag;
  $('stats').textContent = `${frag.length} characters in the fragment · ${n} bars · ${bits} bits/bar`;
  const warn = $('warn');
  if (url.length > URL_WARN_LEN) {
    warn.hidden = false;
    warn.textContent = `This URL is ${url.length} characters. Some apps truncate links that long. Lower the bars or bits, or share the downloaded SVG instead.`;
  } else warn.hidden = true;

  showWaveform({ q, bits, duration, title });
  if (audioEl) { /* keep audio attached to the new preview */ setProgress(0); }
}

/* ---------- Wire up ---------- */
function downloadSVG() {
  if (!current) return;
  const svg = '<?xml version="1.0" encoding="UTF-8"?>\n' + buildSVG(current.q, current.bits, { standalone: true });
  const a = document.createElement('a');
  a.href = URL.createObjectURL(new Blob([svg], { type: 'image/svg+xml' }));
  a.download = (current.title || 'waveform').replace(/[^\w\-]+/g, '_') + '.svg';
  document.body.appendChild(a); a.click(); a.remove();
  setTimeout(() => URL.revokeObjectURL(a.href), 1000);
}
async function copyLink() {
  const box = $('urlBox');
  try { await navigator.clipboard.writeText(box.value); }
  catch { box.select(); document.execCommand('copy'); }
  $('copyBtn').textContent = 'Copied!';
  setTimeout(() => $('copyBtn').textContent = 'Copy link', 1500);
}

$('playBtn').addEventListener('click', togglePlay);
$('waveWrap').addEventListener('pointerdown', e => {
  seekFromEvent(e);
  const move = ev => seekFromEvent(ev);
  const up = () => { window.removeEventListener('pointermove', move); window.removeEventListener('pointerup', up); };
  window.addEventListener('pointermove', move);
  window.addEventListener('pointerup', up);
});
document.addEventListener('keydown', e => {
  if (e.code === 'Space' && !/INPUT|TEXTAREA|SELECT/.test(e.target.tagName)) { e.preventDefault(); togglePlay(); }
});
$('audioLocal').addEventListener('change', e => e.target.files[0] && attachAudio(e.target.files[0]));
$('audioGen').addEventListener('change', e => handleGenFile(e.target.files[0]));
['bars', 'bits'].forEach(id => $(id).addEventListener('input', regenerate));
$('title').addEventListener('change', regenerate);
$('copyBtn').addEventListener('click', copyLink);
$('svgBtn').addEventListener('click', downloadSVG);

const drop = $('drop');
['dragenter', 'dragover'].forEach(ev => drop.addEventListener(ev, e => { e.preventDefault(); drop.classList.add('over'); }));
['dragleave', 'drop'].forEach(ev => drop.addEventListener(ev, e => { e.preventDefault(); drop.classList.remove('over'); }));
drop.addEventListener('drop', e => handleGenFile(e.dataTransfer.files[0]));

window.addEventListener('hashchange', () => { if (!decodedBuffer) loadFromHash(); });
loadFromHash();
})();
