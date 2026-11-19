(function () {
'use strict';
const CABINET_KEYS = {
  P1_U: ['w'],
  P1_D: ['s'],
  P1_L: ['a'],
  P1_R: ['d'],
  P1_1: ['u'],
  P1_2: ['i'],
  P1_3: ['o'],
  P1_4: ['j'],
  P1_5: ['k'],
  P1_6: ['l'],
  P2_U: ['ArrowUp'],
  P2_D: ['ArrowDown'],
  P2_L: ['ArrowLeft'],
  P2_R: ['ArrowRight'],
  P2_1: ['r'],
  P2_2: ['t'],
  P2_3: ['y'],
  P2_4: ['f'],
  P2_5: ['g'],
  P2_6: ['h'],
  START1: ['Enter'],
  START2: ['2'],
};

const { sin, cos, abs, min, max, floor, round, sqrt, atan2, hypot, random, PI, exp, ceil, tan } = Math;
const TAU = PI * 2;
const clamp = (v, a, b) => v < a ? a : v > b ? b : v;
const wrapA = a => atan2(sin(a), cos(a));
const N = 1024, M = N - 1;
const wr = d => ((d % N) + N * 1.5) % N - N / 2;
const wp = v => (v % N + N) % N;
let sd = 1;
const rnd = () => ((sd = Math.imul(sd, 1664525) + 1013904223 | 0) >>> 0) / 4294967296;
const hs = (x, y) => { let h = Math.imul(x, 374761393) + Math.imul(y, 668265263) | 0; h = Math.imul(h ^ h >>> 13, 1274126177); return ((h ^ h >>> 16) >>> 0) / 4294967296; };
const hx = n => (0xff000000 | (n & 255) << 16 | n & 0xff00 | n >> 16 & 255) >>> 0;
const dk = (c, f) => (0xff000000 | min(255, (c >> 16 & 255) * f) << 16 | min(255, (c >> 8 & 255) * f) << 8 | min(255, (c & 255) * f)) >>> 0;
const mk = (w, h) => { const c = document.createElement('canvas'); c.width = w; c.height = h; const g = c.getContext('2d'); g.imageSmoothingEnabled = false; return c; };
const cx2 = c => c.getContext('2d');
const disc = (g, x, y, r, col) => { g.fillStyle = col; for (let v = -r; v <= r; v++) { const w = round(sqrt(max(0, r * r - v * v))); g.fillRect(round(x - w), round(y + v), w * 2 + 1, 1); } };

const nk = k => (k || '').length == 1 ? k.toLowerCase() : k || '';
const KM = {}, IU = 0, ID = 1, IL = 2, IR = 3, I1 = 4, I2 = 5, I3 = 6, IS = 7;
const FLG = { P1_U: IU, P1_D: ID, P1_L: IL, P1_R: IR, P1_1: I1, P1_2: I2, P1_3: I3, START1: IS };
for (const c in CABINET_KEYS) if (c in FLG) for (const k of CABINET_KEYS[c]) KM[nk(k)] = FLG[c];
const HD = new Uint8Array(8), PQ = new Uint8Array(8), PR = new Uint8Array(8);
addEventListener('keydown', e => { aInit(); const f = KM[nk(e.key)]; if (f == null) return; e.preventDefault(); if (!HD[f]) { HD[f] = 1; PQ[f] = 1; } });
addEventListener('keyup', e => { const f = KM[nk(e.key)]; if (f != null) HD[f] = 0; });
addEventListener('blur', () => HD.fill(0));
document.addEventListener('visibilitychange', () => { HD.fill(0); try { AC && (document.hidden ? AC.suspend() : AC.resume()); } catch (e) { } });

let AC, MG, EF, EG, EO, NB;
function aInit() {
  try {
    if (!AC) {
      AC = new (window.AudioContext || window.webkitAudioContext)();
      MG = AC.createGain(); MG.gain.value = .45; MG.connect(AC.destination);
      const len = AC.sampleRate; NB = AC.createBuffer(1, len, len); const d = NB.getChannelData(0);
      for (let i = 0; i < len; i++) d[i] = random() * 2 - 1;
      const src = AC.createBufferSource(); src.buffer = NB; src.loop = true;
      EF = AC.createBiquadFilter(); EF.type = 'bandpass'; EF.Q.value = .9;
      EG = AC.createGain(); EG.gain.value = 0;
      EO = AC.createOscillator(); EO.type = 'sawtooth';
      const lp = AC.createBiquadFilter(); lp.frequency.value = 260; const og = AC.createGain(); og.gain.value = .5;
      src.connect(EF); EF.connect(EG); EO.connect(lp); lp.connect(og); og.connect(EG); EG.connect(MG);
      src.start(); EO.start();
    }
    if (AC.state == 'suspended') AC.resume();
  } catch (e) { }
}
function tone(f, f2, d, ty, v, dl) {
  if (!AC) return;
  const t = AC.currentTime + (dl || 0), o = AC.createOscillator(), g = AC.createGain();
  o.type = ty || 'square'; o.frequency.setValueAtTime(f, t); o.frequency.exponentialRampToValueAtTime(f2, t + d);
  g.gain.setValueAtTime(v, t); g.gain.exponentialRampToValueAtTime(.001, t + d);
  o.connect(g); g.connect(MG); o.start(t); o.stop(t + d + .02); o.onended = () => g.disconnect();
}
let NT = 0, NI = 0;
const CHR = [0, -4, 3, -2], MAJ = [0, 4, 7, 12], MIN = [0, 3, 7, 12], MEL = [12, 0, 7, 0, 15, 12, 10, 7];
function music() {
  if (!AC || MODE != 1) { NT = 0; return; }
  const t = AC.currentTime, st = .13 - min(LEVEL, 6) * .006;
  if (NT < t) NT = t + .05;
  while (NT < t + .25) {
    const i = NI++ & 63, cr = CHR[i >> 4], iv = i >> 4 ? MAJ : MIN, f = n => 220 * 2 ** ((cr + n) / 12), d = NT - t;
    if (i % 4 == 0) tone(f(-24), f(-24), st * 3, 'triangle', .16, d);
    if (i % 2 == 0) tone(f(iv[(i >> 1) % 4]), f(iv[(i >> 1) % 4]), st * .9, 'square', .035, d);
    if (i % 8 == 6 && LEVEL > 0) tone(f(MEL[(i >> 3) % 8]), f(MEL[(i >> 3) % 8]), st * 1.8, 'triangle', .07, d);
    if (i % 4 == 2) noise(.04, 6000, 3000, .05, 'highpass', d);
    NT += st;
  }
}
function noise(d, f, f2, v, ty, dl) {
  if (!AC) return;
  const t = AC.currentTime + (dl || 0), s = AC.createBufferSource(), fl = AC.createBiquadFilter(), g = AC.createGain();
  s.buffer = NB; s.loop = true; fl.type = ty || 'lowpass'; fl.frequency.setValueAtTime(f, t); fl.frequency.exponentialRampToValueAtTime(f2, t + d);
  g.gain.setValueAtTime(v, t); g.gain.exponentialRampToValueAtTime(.001, t + d);
  s.connect(fl); fl.connect(g); g.connect(MG); s.start(t); s.stop(t + d); s.onended = () => g.disconnect();
}

const HK = 'vuelo-austral-hs';
let HS = [], LASTI = -1;
const vhs = v => {
  const a = Array.isArray(v) ? v : v && Array.isArray(v.top) ? v.top : [];
  return a.filter(r => r && typeof r.n == 'string' && /^[A-Z0-9 ]{3}$/.test(r.n) && Number.isInteger(r.s) && r.s >= 0 && r.s < 1e9).map(r => ({ n: r.n, s: r.s })).sort((a, b) => b.s - a.s).slice(0, 5);
};
const STO = () => window.platanusArcadeStorage || { get: k => { const v = localStorage.getItem(k); return v == null ? { found: false } : { found: true, value: JSON.parse(v) }; }, set: (k, v) => localStorage.setItem(k, JSON.stringify(v)) };
function hsLoad() { try { Promise.resolve(STO().get(HK)).then(r => { if (r && r.found) HS = vhs(HS.concat(vhs(r.value))); }).catch(() => { }); } catch (e) { } }
function hsSave() { try { Promise.resolve(STO().set(HK, { v: 1, top: HS })).catch(() => { }); } catch (e) { } }

const COL = new Uint32Array(N * N), HV = new Uint8Array(N * N), DP = new Uint8Array(N * N), VR = new Uint8Array(N * N), LHH = 14;
let MAPC, WAV = [], LH = [];
function genWorld() {
  sd = 7331;
  const H = new Float32Array(N * N); let amp = 1;
  for (let cl = 128; cl >= 2; cl >>= 1, amp *= .5) {
    const g = N / cl, L = new Float32Array(g * g);
    for (let i = 0; i < g * g; i++) L[i] = rnd();
    for (let y = 0; y < N; y++) {
      const gy = y / cl, iy = gy | 0; let fy = gy - iy; fy = fy * fy * (3 - 2 * fy);
      const r0 = iy * g, r1 = (iy + 1) % g * g;
      for (let x = 0, o = y * N; x < N; x++) {
        const gx = x / cl, ix = gx | 0; let fx = gx - ix; fx = fx * fx * (3 - 2 * fx);
        const i1 = (ix + 1) % g, a = L[r0 + ix] + (L[r0 + i1] - L[r0 + ix]) * fx, b = L[r1 + ix] + (L[r1 + i1] - L[r1 + ix]) * fx;
        H[o + x] += (a + (b - a) * fy) * amp;
      }
    }
  }
  let mn = 1e9, mx = -1e9;
  for (let i = 0; i < N * N; i++) { const v = H[i]; if (v < mn) mn = v; if (v > mx) mx = v; }
  const hist = new Uint32Array(256);
  for (let i = 0; i < N * N; i++) { H[i] = (H[i] - mn) / (mx - mn); hist[H[i] * 255 | 0]++; }
  let acc = 0, k = 0; while (acc < N * N * .7) acc += hist[k++];
  const SL = k / 255;
  const [DEEP, SEA, SH1, SH2, SURF, SAND, WSAND, G0, G1, G2, G3, R1, R2, SNOW, TQ] = [0x2259a8, 0x2a67b8, 0x3482cc, 0x4aa2dc, 0xf2faff, 0xead7a2, 0xd9c28a, 0x96d24e, 0x74bd40, 0x58a633, 0x428e2c, 0xa29d93, 0x8b857c, 0xf0f0ea, 0x68ccd6].map(hx);
  const GR = [G0, G1, G2, G3];
  const band = e => e * (e < .5 ? 9 : 17) | 0;
  for (let y = 0; y < N; y++) for (let x = 0; x < N; x++) {
    const i = y * N + x, h = H[i], n = hs(x, y); let c;
    if (h < SL) {
      const d = (SL - h) / SL; DP[i] = min(255, d * 900);
      c = d < .006 + n * .01 ? (n > .3 ? SURF : TQ) : d < .016 + (n - .5) * .008 ? TQ : d < .034 + (n - .5) * .012 ? SH2 : d < .075 + (n - .5) * .02 ? SH1 : d > .3 + (n - .5) * .03 ? DEEP : SEA;
    } else {
      const e = (h - SL) / (1 - SL); HV[i] = e * 72;
      const b = band(e);
      c = e < .012 + n * .006 ? WSAND : e < .03 + n * .012 ? SAND : e < .5 ? GR[clamp((e - .03) * 8 + (n - .5) * .9, 0, 3) | 0] : e < .8 ? (b & 1 ? R1 : R2) : SNOW;
      const er = (H[y * N + (x + 1 & M)] - SL) / (1 - SL), ed = (H[(y + 1 & M) * N + x] - SL) / (1 - SL);
      if (e > .05 && (band(er) != b || band(ed) != b)) c = dk(c, e < .5 ? .86 : .8);
    }
    COL[i] = c;
  }
  const vn = (x, y, cl) => { const g = N / cl, gx = x / cl, gy = y / cl, ix = gx | 0, iy = gy | 0, fx = gx - ix, fy = gy - iy, a = hs(ix % g, iy % g), b = hs((ix + 1) % g, iy % g), c = hs(ix % g, (iy + 1) % g), d = hs((ix + 1) % g, (iy + 1) % g); return a + (b - a) * fx + (c - a + (a - b - c + d) * fx) * fy; };
  VR.set(HV);
  const [TL, TM, TD, TS] = [0x5aa83c, 0x2f7d33, 0x1d5428, 0x144026].map(hx);
  for (let y = 0; y < N; y += 4) for (let x = 0; x < N; x += 4) {
    const px = x + (hs(x, y + 7) * 4 | 0), py = y + (hs(x + 5, y) * 4 | 0), i = (py & M) * N + (px & M), e = HV[i] / 72;
    if (e < .05 || e > .46) continue;
    const m = vn(px, py, 64);
    if (m < .5 || hs(px, py + 1) > (m - .45) * 3) continue;
    const r = 2 + (hs(px + 3, py) * 2.4 | 0), top = HV[i] + 2 + r * .5;
    for (let v = -r; v <= r + 1; v++) for (let u = -r; u <= r + 1; u++) {
      const q = (py + v & M) * N + (px + u & M), d2 = u * u + v * v, s2 = (u - 1) * (u - 1) + (v - 1) * (v - 1);
      if (d2 <= r * r + .6) {
        COL[q] = u + v < -r * .5 ? TL : u + v > r * .6 ? TD : (u + v + 99 & 1) && (u ^ v) & 1 ? TD : TM; HV[q] = max(HV[q], top); VR[q] = max(VR[q], HV[i] + 1);
      } else if (s2 <= r * r + .6 && !DP[q]) COL[q] = TS;
    }
  }
  sd = 99;
  for (let t = 0, f = 0; t < 4e4 && f < 8; t++) {
    const x = rnd() * N | 0, y = rnd() * N | 0, i = y * N + x, e = HV[i] / 72;
    if (e < .02 || e > .07 || !DP[y * N + (x + 5 & M)] || !DP[(y + 5 & M) * N + x]) continue;
    f++; LH.push(x, y);
    for (let v = -1; v <= 1; v++) for (let u = -1; u <= 1; u++) { const q = (y + v & M) * N + (x + u & M); COL[q] = hx(u | v ? 0xf0f0ea : 0xd83a2a) & 0xfeffffff; HV[q] = HV[i] + 20; VR[q] = HV[i] + LHH; }
  }
  const ROOF = [0xd8483a, 0xf0c040, 0x4a7ad8, 0x58b45a, 0xe8e8e0].map(hx), STILT = hx(0x5a3a22);
  for (let t = 0, f = 0; t < 6e4 && f < 10; t++) {
    const x = rnd() * N | 0, y = rnd() * N | 0, i = y * N + x;
    if (DP[i] || HV[i] > 2 || !DP[(y + 3 & M) * N + x] || !DP[(y + 3 & M) * N + (x + 12 & M)] || DP[y * N + (x + 12 & M)]) continue;
    f++;
    for (let h = 0; h < 4; h++) {
      const rc = ROOF[(f + h) % 5], hx0 = x + h * 4;
      for (let v = 0; v < 4; v++) for (let u = 0; u < 3; u++) {
        const q = (y + 1 + v & M) * N + (hx0 + u & M);
        if (v < 2) { COL[q] = v ? dk(rc, .75) : rc; VR[q] = HV[q] = max(HV[q], 6); } else if (v == 2) COL[q] = hx(0x8a6a4a); else if (u != 1) COL[q] = STILT;
      }
    }
  }
  MAPC = mk(N, N);
  cx2(MAPC).putImageData(new ImageData(new Uint8ClampedArray(COL.buffer.slice(0)), N, N), 0, 0);
  const WC = [0xffffff, 0xffffff, 0xa8d8ff].map(hx);
  for (let k = 0; k < 3; k++) {
    const A = new Uint32Array(N * N);
    for (let j = 0; j < N * N / 130; j++) {
      const x = rnd() * N | 0, y = rnd() * N | 0, i = y * N + x;
      if (DP[i] < 30 || DP[y * N + (x + 8 & M)] < 30 || DP[y * N + (x - 2 & M)] < 30) continue;
      const len = 1 + (rnd() * 3 | 0), c = WC[rnd() * 3 | 0];
      for (let u = 0; u < len; u++) { A[y * N + (x + u & M)] = c; if (!k) COL[y * N + (x + u & M)] = c; }
      if (len > 2 && rnd() < .5) A[(y - 1 & M) * N + (x + 2 & M)] = c;
    }
    const cv = mk(N, N); cx2(cv).putImageData(new ImageData(new Uint8ClampedArray(A.buffer), N, N), 0, 0); WAV.push(cv);
  }
}

const NF = 32;
let JET, JSH, JREAR, JLAY = [];
const jm = (x, y, z) => {
  const a = abs(y);
  if (x < 0 || x > 21) return 0;
  if (x >= 12 && x <= 16.5 && a < 1.2 && z > .9 && z < 2.4 - abs(x - 14) * .3) return 5;
  const fw = x > 15 ? (21.6 - x) * .36 : x < 1.5 ? 1.3 : 2.1, ft = x > 16 ? 1.4 - (x - 16) * .18 : 1.4;
  if (a <= fw && z >= -1.3 && z <= ft) return x < 1 ? 6 : x > 19.5 ? 3 : z < 0 ? 7 : a < .5 && x > 2 && x < 12 ? 3 : 1;
  if (x >= .5 && x <= 6.5 && a < .7 && z > 0 && z <= 1.6 + (6.5 - x) * .95) return z > 5 ? 4 : 3;
  const sp = x >= 2 && x <= 13 ? 2 + (13 - x) * .88 : 0;
  if (a <= sp && abs(z + .5) <= .6) return a > sp - 1.6 || a > 8.8 || a > 4.6 && a < 5.8 ? 3 : x < 3.5 ? 4 : 1;
  if (x >= 15 && x <= 17.5 && a <= 2 + (17.5 - x) * 1.25 && abs(z - .5) <= .6) return 4;
  return 0;
};
const JPAL = [0, 0xffd21e, 0, 0x24242c, 0xff7a1a, 0x6fdcff, 0x4a4e58, 0xc99a12].map(hx);
const JG = 32, JK = 1, FLX = -.5 - 10.5 / JK, LO = .8;
function bakeJet() {
  const W = JG * NF, V3 = JG * JG * JG, vol = new Uint8Array(V3), vol0 = new Uint8Array(V3), ix = (z, r, c) => (z * JG + r) * JG + c, h = JG / 2 - .5;
  JET = mk(W, JG * JG); JSH = mk(W, JG);
  const id = cx2(JET).createImageData(W, JG * JG), u = new Uint32Array(id.data.buffer), id2 = cx2(JSH).createImageData(W, JG), u2 = new Uint32Array(id2.data.buffer), SHC = hx(0x0a1e44);
  for (let f = 0; f < NF; f++) {
    const r = f / NF * TAU, c = cos(r) * JK, s = sin(r) * JK;
    let l0 = 99, l1 = -1;
    for (let zl = 0; zl < JG; zl++) for (let row = 0; row < JG; row++) for (let col = 0; col < JG; col++) {
      const z = zl - h, y = row - h;
      vol[ix(zl, row, col)] = jm((col - 15.5) * JK + 10.5, y * c - z * s, y * s + z * c);
    }
    if (!f) vol0.set(vol);
    for (let zl = 0; zl < JG; zl++) for (let row = 0; row < JG; row++) for (let col = 0; col < JG; col++) {
      const v = vol[ix(zl, row, col)]; if (!v) continue;
      const top = zl == JG - 1 || !vol[ix(zl + 1, row, col)];
      u[(zl * JG + row) * W + f * JG + col] = dk(JPAL[v], top ? 1 : .68);
      u2[row * W + f * JG + col] = SHC;
      if (zl < l0) l0 = zl; if (zl > l1) l1 = zl;
    }
    JLAY.push([l0, l1]);
  }
  cx2(JET).putImageData(id, 0, 0); cx2(JSH).putImageData(id2, 0, 0);
  JREAR = mk(JG, 44);
  const id3 = cx2(JREAR).createImageData(JG, 44), u3 = new Uint32Array(id3.data.buffer);
  for (let col = JG - 1; col >= 0; col--) for (let zl = 0; zl < JG; zl++) for (let row = 0; row < JG; row++) {
    const v = vol0[ix(zl, row, col)]; if (!v) continue;
    const top = zl == JG - 1 || !vol0[ix(zl + 1, row, col)], back = !col || !vol0[ix(zl, row, col - 1)];
    const py = round(JG - 1 - zl + (JG - col) * .32);
    if (py >= 0 && py < 44) u3[py * JG + row] = dk(JPAL[v], top ? 1.05 : back ? .82 : .6);
  }
  cx2(JREAR).putImageData(id3, 0, 0);
}

let CLD = [], CSH = [], CSD = [], BANS, LIFE, ARW, FLM, FLR, FONT, PANEL, RADC, BALLC;
function bakeCloud(seed) {
  sd = seed;
  const W = 72, H = 56, a = mk(W, H), b = mk(W, H), c = mk(W, H), ga = cx2(a), gb = cx2(b), gc = cx2(c), P = [];
  const n = 5 + rnd() * 5 | 0;
  for (let i = 0; i < n; i++) { const x = 12 + rnd() * 48, e = 1 - abs(x - 36) / 30; P.push([x, 30 + rnd() * 10 - e * 4, 3 + (e * 4 + rnd() * 3) | 0]); }
  P.sort((p, q) => p[1] - q[1]);
  for (const [x, y, R] of P) {
    disc(gb, x, y, R, '#0a2a5e');
    disc(gc, x, y, R, '#b9c8e0'); disc(gc, x - 1, y - 2, R - 1, '#e8eef8'); disc(gc, x - 2, y - 3, R - 3, '#fff');
  }
  for (const [x, y, R] of P) for (let z = 0; z <= R * 2; z++) {
    const zz = z - R, rs = round(sqrt(R * R - zz * zz)), t = z / (2 * R);
    if (rs < 1) continue;
    if (z % 2 == 0) disc(ga, x - t * 2, y - z * .45 + 1, rs, t < .4 ? '#8ea2c4' : '#c4d2ea');
    disc(ga, x - t * 2, y - z * .45, rs, t < .3 ? '#b4c4de' : t < .55 ? '#dbe4f3' : t < .8 ? '#f1f5fb' : '#fff');
  }
  CLD.push(a); CSH.push(b); CSD.push(c);
}
function bmp(str, w, pal, ol) {
  const h = str.length / w, c = mk(w + 2, h + 2), g = cx2(c);
  for (let p = 0; p < 2; p++) for (let i = 0; i < str.length; i++) {
    const v = '.ybowk'.indexOf(str[i]); if (v < 1) continue;
    const x = i % w + 1, y = i / w + 1 | 0;
    if (p) { g.fillStyle = pal[v]; g.fillRect(x, y, 1, 1); } else if (ol) { g.fillStyle = ol; g.fillRect(x - 1, y, 3, 1); g.fillRect(x, y - 1, 1, 3); }
  }
  return c;
}
const FCH = "0123456789 ABCDEFGHIJKLMNOPQRSTUVWXYZ.:-!/+*<>'?,%^v";
const FDAT = 'odr8t3jhjjgui4po0ebfzmmqohboge0008odl9qbabl7yo13o10bcbi5pn133myi3xeg7iy5l7x8kql9g8kzl9pb66n0yi27i22i65hwthw2mnb0020sw0cg77m3ok15c23s45tdhw740jgi03kd5t9fk0e2';
const Y3 = ['#ffd21e', '#4dff6a', '#ff6a1a'];
const TCOL = ['#ffffff', '#ffd21e', '#ff8a2a', '#8fe3ff', '#ff5050', '#7dff6a', '#a8b4c8', '#10121e', '#3cff8a'];
function bakeMisc() {
  for (let i = 0; i < 8; i++) bakeCloud(17 + i * 31);
  BANS = bmp('......b......yo......yyo....yyyo...yyyo..yyyyo..byyoo....bo.....', 8, [0, '#ffd21e', '#6a4410', '#d89a10'], '#3a2408');
  LIFE = bmp('....y........y.......yyy.....yyyyyyy.yyyyyyyyy...yyy.....o.y.o..', 9, [0, '#ffd21e', 0, '#ff7a1a'], '#10121e');
  ARW = mk(272, 51);
  const ag = cx2(ARW);
  for (let k = 0; k < 3; k++) for (let r = 0; r < 16; r++) for (let p = 0; p < 2; p++) for (let y = -8; y <= 8; y++) for (let x = -8; x <= 8; x++) {
    const a = r / 16 * TAU, u = x * cos(a) + y * sin(a), v = abs(y * cos(a) - x * sin(a));
    if (u > 6.5 || u < -6 || v > (u > 0 ? (6.5 - u) * .9 : 1.6)) continue;
    ag.fillStyle = p ? Y3[k] : '#10121e'; ag.fillRect(r * 17 + 7 + x + p, k * 17 + 7 + y + p, 3 - p * 2, 3 - p * 2);
  }
  FLM = mk(30, 3);
  const fg = cx2(FLM);
  for (let f = 0; f < 3; f++) for (let x = 0; x < 10; x++) {
    fg.fillStyle = x > 6 ? '#fff6c0' : x > 2 ? '#ffd21e' : '#ff8a1a'; if (x > f) fg.fillRect(f * 10 + x, 1, 1, 1);
    if (x > 3 + f) { fg.fillStyle = '#ff6a1a'; fg.fillRect(f * 10 + x, 0, 1, 1); fg.fillRect(f * 10 + x, 2, 1, 1); }
  }
  FLR = mk(21, 7);
  const rg = cx2(FLR);
  for (let f = 0; f < 3; f++) for (let y = 0; y < 7; y++) for (let x = 0; x < 7; x++) {
    const d = hypot(x - 3, y - 3); if (d > 3.4 - f * .35) continue;
    rg.fillStyle = d < 1.2 ? '#fffbe0' : d < 2.2 ? '#ffd21e' : '#ff6a1a'; rg.fillRect(f * 7 + x, y, 1, 1);
  }
  FONT = mk(FCH.length * 4, TCOL.length * 6);
  const tg = cx2(FONT);
  TCOL.forEach((c, ci) => { tg.fillStyle = c; for (let i = 0; i < FCH.length; i++) { const b = parseInt(FDAT.substr(i * 3, 3), 36); for (let p = 0; p < 15; p++) if (b >> 14 - p & 1) tg.fillRect(i * 4 + p % 3, ci * 6 + (p / 3 | 0), 1, 1); } });
}

const W3 = 267, H3 = 200, FOC = W3 / 1.4, D3 = 420, SKN = H3 * 2;
const SKY = new Uint32Array(SKN), PT = new Int16Array(W3);
const [FR, FG, FB] = [0xd6, 0xea, 0xf5];
function bakeSky() {
  for (let k = 0; k < SKN; k++) {
    if (k >= H3) { SKY[k] = hx(0xd6eaf5); continue; }
    const t = min(1, (H3 - k) / 120), q = clamp(floor(t * 7 + (k & 1 ? .3 : -.3)), 0, 7) / 7;
    SKY[k] = (0xff000000 | (0xf5 + (0xe6 - 0xf5) * q) << 16 | (0xea + (0x9e - 0xea) * q) << 8 | (0xd6 + (0x58 - 0xd6) * q)) >>> 0;
  }
}
function bakePanel() {
  PANEL = mk(W3, H3);
  const g = cx2(PANEL), R = (c, x, y, w, h) => { g.fillStyle = c; g.fillRect(x, y, w, h); };
  for (let y = 0; y < 140; y++) {
    const w = round(5 + 34 * max(0, 1 - y / 46) ** 2);
    R('#1c1f25', 0, y, w, 1); R('#1c1f25', W3 - w, y, w, 1); R('#4a515c', w, y, 1, 1); R('#4a515c', W3 - w - 1, y, 1, 1);
    if (y % 30 == 15) { R('#ff6a1a', 1, y, 3, 3); R('#ff6a1a', W3 - 4, y, 3, 3); }
  }
  for (let x = 0; x < W3; x++) {
    const d = abs(x - 133), yt = d < 46 ? 131 : d < 54 ? 131 + d - 46 : 139;
    PT[x] = yt;
    R('#2a2e36', x, yt, 1, H3 - yt); R('#5b636e', x, yt, 1, 2); R('#16181d', x, yt + 2, 1, 1);
    if (d < 44) for (let y = 134; y < 137; y++) R((x + y >> 2 & 1) ? '#ffd21e' : '#111216', x, y, 1, 1);
  }
  R('#15171c', 10, 150, 64, 46); R('#15171c', 193, 150, 64, 46);
  R('#3a3f48', 11, 151, 62, 1); R('#3a3f48', 194, 151, 62, 1);
  R('#06281a', 13, 153, 58, 40); R('#06281a', 196, 153, 58, 40);
  for (let y = -20; y <= 20; y++) for (let x = -20; x <= 20; x++) {
    const d = hypot(x, y);
    if (d <= 19.5 && d > 16.5) R(d > 18.5 ? '#111216' : y < 0 ? '#a0a8b4' : '#6d7580', 133 + x, 170 + y, 1, 1);
    for (const gx of [97, 169]) { if (d <= 11.5) R(d > 10.5 ? '#7d8590' : '#0d0f12', gx + x, 170 + y, 1, 1); }
  }
  for (const gx of [97, 169]) for (let a = 0; a < 9; a++) { const t = -3.9 + a * .975; R('#e8eef6', gx + round(cos(t) * 9), 170 + round(sin(t) * 9), 1, 1); }
  for (let i = 0; i < 5; i++) R('#3a2a1a', 112 + i * 9, 141, 7, 3);
  R('#1a1c21', 0, 196, W3, 4);
  for (const [x, y] of [[6, 146], [W3 - 7, 146], [6, 192], [W3 - 7, 192], [80, 190], [W3 - 81, 190]]) R('#8a929e', x, y, 1, 1);
  RADC = mk(58, 40); BALLC = mk(33, 33);
}

let S, OVT, OG, OVI, P3T, P3G, P3D, U3, P3I, HT, HG, HUI, RADD, R32, BALD, B32;
let MODE = 0, MT = 0, TT = 0, VIEW = 0, VLOCK = 0, DEMO = 1, TSHOW = 0, GOR = 0, SHK = 0;
let JX = 300, JY = 300, JA = 0, ALT = 40, VS = 0, SPD = 42, BANK = 0, ROLL = 0, RT = 0, RDIR = 1, RCD = 0, SIDE = 0, BOOST = 1, THR = 0, INV = 0, SAFE = 0, DEAD = 0, G0 = 0, PITCH = 0;
let SCORE = 0, TIME = 45, LIVES = 3, LEVEL = 0, GATES = 0, CHAIN = 0, CHT = 0, MULT = 1, LOWT = 0, LOWC = 0, PLAYT = 0, BEEP = 0;
let GX = 0, GY = 0, GA = 40, GDX = 1, GDY = 0, GR = 13, GSIDE = 0, BIRDT = 8, WX = 0, WY = 0, WTX = 0, WTY = 0, WT = 6;
let ZS = 3, SC = 1, CX = 0, CY = 0, ZC = 200, PX = 0, PY = 0, PK = 1, PZ = 0;
let CAMA = 0, CAMALT = 50, C3x = 0, C3y = 0, C3alt = 0, C3ca = 1, C3sa = 0, C3hor = 0, C3tr = 0, TRT = 0;
let NM = [0, 0, 0], NP = 0, RH = 0, RN = 0, GW = 0, WARN = 0, BW = 0;
const BASE = 42, HC = 190, FZ = 3.4 * 194, SUNX = .22, SUNY = .3;
const NBN = 40, BN = new Float32Array(NBN * 4), BTOL = 10; let BNI = 0;
const LHC = new Uint32Array(17), LT = new Uint8Array(5);
for (let l = 0; l < 17; l++) LHC[l] = hx(l > 15 ? 0x58a633 : l > 14 ? 0xfff6a0 : l > 13 ? 0x22242a : l < 2 ? 0x6b6f78 : (l >> 1 & 1) ? 0xd83a2a : 0xf4f4f0);
const NBD = 12, BD = new Float32Array(NBD * 6);
const NPT = 60, PA = new Float32Array(NPT * 7);
const TN = 220, TR = new Float32Array(TN * 7); let TH = 0, TCN = 0;
const NC = 110, CL = new Float32Array(NC * 4), CZ = new Float32Array(NC), CI = new Uint16Array(NC);
const MSG = [['', 0, 0], ['', 0, 0], ['', 0, 0]];
const TA = [.95, .65, .38, .16], GRN = [0x0e4a2a, 0x1f7a3e, 0x3fae52, 0x8fe08a].map(hx), LC = ['#ff8a1a', '#4dff6a', '#ffd21e', '#ff3a2a', '#8fe3ff'];
const AL = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789 ', VSEQ = [0, 0, 1, 0, 2];

const gh = (x, y) => HV[((y | 0) & M) * N + ((x | 0) & M)];
const msg = (t, c) => { const b = MSG.pop(); b[0] = t; b[1] = 1.6; b[2] = c; MSG.unshift(b); };

function placeClouds() {
  sd = 4242;
  const P = [];
  for (let i = 0; i < 30; i++) {
    const x = rnd() * N, y = rnd() * N, n = 1 + rnd() * 4 | 0;
    for (let j = 0; j < n && P.length < NC; j++) P.push([wp(x + (rnd() - .5) * 80), wp(y + (rnd() - .5) * 50), 35 + rnd() * 50, rnd() * 8 | 0]);
  }
  while (P.length < NC) P.push([rnd() * N, rnd() * N, 35 + rnd() * 50, rnd() * 8 | 0]);
  P.sort((a, b) => a[2] - b[2]).forEach((p, i) => CL.set(p, i * 4));
}

function newGate(first) {
  const bx = GX, by = GY, ba = GA;
  const dir = atan2(GDY, GDX) + (random() - .5) * (first ? .5 : 2.4), dist = (first ? 120 : 150 + min(LEVEL, 12) * 14) + random() * 70;
  GX = wp(bx + cos(dir) * dist); GY = wp(by + sin(dir) * dist); GDX = cos(dir); GDY = sin(dir);
  GR = max(8.5, 13 - LEVEL * .35);
  let gm = 0;
  for (let a = 0; a < 8; a++) gm = max(gm, gh(GX + cos(a) * (GR + 5), GY + sin(a) * (GR + 5)));
  gm = max(gm, gh(GX, GY));
  GA = clamp(random() < .3 ? gm + GR + 3 : gm + GR + 4 + random() * (30 + LEVEL * 6), 14, 112);
  const low = random() < .35, amp = (random() - .5) * 80;
  for (let k = 1; k <= 6; k++) {
    const t = k / 7, o = BNI * 4, x = wp(bx + wr(GX - bx) * t - GDY * sin(t * PI) * amp), y = wp(by + wr(GY - by) * t + GDX * sin(t * PI) * amp);
    BN[o] = x; BN[o + 1] = y; BN[o + 2] = max(gh(x, y) + 6, low ? 0 : ba + (GA - ba) * min(1, t * 1.6) + sin(t * PI) * 5); BN[o + 3] = 1;
    BNI = (BNI + 1) % NBN;
  }
  GSIDE = 0;
}

function reset(demo) {
  DEMO = demo;
  for (let t = 0; t < 999; t++) { JX = random() * N; JY = random() * N; if (DP[(JY | 0) * N + (JX | 0)] > 60) break; }
  JA = random() * TAU; ALT = 45; VS = 0; SPD = BASE; BANK = 0; ROLL = 0; RT = 0; RCD = 0; SIDE = 0; BOOST = 1; INV = 0; SAFE = 0; DEAD = 0;
  SCORE = 0; TIME = 40; LIVES = 3; LEVEL = 0; GATES = 0; CHAIN = 0; CHT = 0; MULT = 1; LOWT = 0; LOWC = 0; PLAYT = 0; WX = WY = WTX = WTY = 0; WT = 6; BIRDT = 10;
  BN.fill(0); BD.fill(0); PA.fill(0); TCN = 0; CAMA = JA; CAMALT = ALT + 9;
  GX = JX; GY = JY; GA = ALT; GDX = cos(JA); GDY = sin(JA); newGate(1);
}

function startGame() {
  reset(0); MODE = 1; MT = 0; if (!VLOCK) VIEW = 0; VLOCK = 1;
  tone(523, 523, .1, 0, .15); tone(659, 659, .1, 0, .15, .1); tone(784, 1568, .3, 0, .15, .2);
  msg('A VOLAR!', 1);
}

function gameOver(r) {
  MODE = 2; MT = 0; GOR = r; DEMO = 1; SCORE |= 0; LEVEL = 0; WARN = 0;
  tone(440, 110, 1.2, 'triangle', .3);
}

function crash() {
  if (DEAD > 0) return;
  DEAD = 1.8; SHK = .5; CHAIN = 0;
  if (!DEMO) { LIVES--; msg('CHOQUE!', 4); }
  for (let i = 0; i < NPT; i++) {
    const o = i * 7, a = random() * TAU, b = random() * 2 - 1, v = 10 + random() * 30;
    PA.set([JX, JY, ALT, cos(a) * v * sqrt(1 - b * b) + cos(JA) * SPD * .4, sin(a) * v * sqrt(1 - b * b) + sin(JA) * SPD * .4, b * v + 8, .7 + random()], o);
  }
  if (!DEMO) { noise(1.2, 1800, 60, .9); tone(160, 30, .9, 'sawtooth', .3); }
}

function step(dt, cl, cr, cu, cd, cb, croll) {
  for (let i = 0; i < NPT; i++) {
    const o = i * 7; if (PA[o + 6] <= 0) continue;
    PA[o] += PA[o + 3] * dt; PA[o + 1] += PA[o + 4] * dt; PA[o + 2] += PA[o + 5] * dt; PA[o + 5] -= 25 * dt; PA[o + 6] -= dt;
  }
  for (let i = 0; i < NBD; i++) {
    const o = i * 6; if (BD[o + 5] <= 0) continue;
    BD[o] = wp(BD[o] + BD[o + 3] * dt); BD[o + 1] = wp(BD[o + 1] + BD[o + 4] * dt); BD[o + 5] -= dt;
    if (DEAD <= 0 && INV <= 0) { const dx = wr(JX - BD[o]), dy = wr(JY - BD[o + 1]), dh = ALT - BD[o + 2]; if (dx * dx + dy * dy + dh * dh < 50) { BD[o + 5] = 0; crash(); } }
  }
  if (DEAD > 0) {
    DEAD -= dt;
    if (DEAD <= 0) {
      if (!DEMO && LIVES <= 0) { DEAD = .01; gameOver(1); return; }
      ALT = clamp(max(ALT, G0 + 30), 30, 110); VS = 0; INV = 2.5; SAFE = 2.5; TCN = 0;
    }
    return;
  }
  const turn = (cr ? 1 : 0) - (cl ? 1 : 0);
  BANK += (turn * .85 - BANK) * min(1, dt * 5);
  JA = wrapA(JA + BANK * 1.9 * dt);
  VS += ((cu ? 38 : cd ? -38 : 0) - VS) * min(1, dt * 4);
  ALT += VS * dt;
  if (ALT > 125) { ALT = 125; VS = min(VS, 0); }
  if (ALT < 3) { ALT = 3; VS = max(VS, 0); }
  PITCH = VS / 50;
  THR = cb && BOOST > .02 ? 1 : 0;
  BOOST = THR ? max(0, BOOST - dt * .38) : min(1, BOOST + dt * .16);
  SPD += (BASE * (THR ? 1.8 : 1) * (1 + min(LEVEL, 12) * .025) - SPD) * min(1, dt * 2.5);
  if (croll && RCD <= 0) { RT = .65; RDIR = turn || -RDIR; RCD = 1.4; INV = max(INV, .75); SIDE = RDIR * 75; DEMO || noise(.45, 300, 2600, .35, 'bandpass'); }
  RCD -= dt; INV -= dt; SAFE -= dt;
  if (RT > 0) RT -= dt;
  SIDE *= exp(-dt * 3.5);
  ROLL = BANK + (RT > 0 ? (1 - RT / .65) * TAU * RDIR : 0);
  const c = cos(JA), s = sin(JA);
  if (!DEMO && LEVEL >= 3) {
    WT -= dt;
    if (WT <= 0) { WT = 4 + random() * 6; const a = random() * TAU, m = random() < .45 ? 0 : 7 + min(LEVEL, 12) * 1.3; WTX = cos(a) * m; WTY = sin(a) * m; }
  } else WTX = WTY = 0;
  WX += (WTX - WX) * min(1, dt); WY += (WTY - WY) * min(1, dt);
  JX = wp(JX + (c * SPD - s * SIDE + WX) * dt); JY = wp(JY + (s * SPD + c * SIDE + WY) * dt);
  G0 = gh(JX, JY);
  const gn = max(G0, gh(JX + c * 8, JY + s * 8));
  if (ALT < gn) { if (SAFE > 0) ALT = gn + .5; else { crash(); return; } }
  GW = max(gn, gh(JX + c * SPD * .6, JY + s * SPD * .6), gh(JX + c * SPD * 1.2, JY + s * SPD * 1.2));
  WARN = GW > ALT - 3 ? WARN + dt : 0;
  if (!DEMO && WARN > 0 && (WARN * 6 | 0) != BW) { BW = WARN * 6 | 0; BW % 2 || tone(1250, 1250, .05, 0, .09); }
  TRT += dt;
  if (TRT > .03) {
    TRT = 0;
    const kq = ZS / 3 * (ALT + HC) / HC, sp = VIEW ? 3.5 : 11 / kq, bk = VIEW ? 1 : 8 / kq, la = sp * cos(ROLL), lh = sp * sin(ROLL), o = TH * 7;
    TR[o] = JX + s * la - c * bk; TR[o + 1] = JY - c * la - s * bk; TR[o + 2] = ALT + lh;
    TR[o + 3] = JX - s * la - c * bk; TR[o + 4] = JY + c * la - s * bk; TR[o + 5] = ALT - lh; TR[o + 6] = TT;
    TH = (TH + 1) % TN; if (TCN < TN) TCN++;
  }
  const rx = wr(JX - GX), ry = wr(JY - GY), side = rx * GDX + ry * GDY, lat = -rx * GDY + ry * GDX, dh = ALT - GA, sg = side >= 0 ? 1 : -1;
  if (GSIDE && sg != GSIDE && abs(side) < 25) {
    if (lat * lat + dh * dh < GR * GR) {
      GATES++; CHAIN++; CHT = 6;
      const tb = max(3, 6.5 - LEVEL * .4);
      if (!DEMO) { TIME = min(50, TIME + tb); SCORE += 500 * MULT; msg('ARO +' + round(tb) + 'S', 5); }
      if (!DEMO) { tone(660, 660, .12, 'sine', .3); tone(880, 880, .12, 'sine', .3, .08); tone(1320, 1320, .3, 'sine', .3, .16); }
      newGate();
    } else if (!DEMO && abs(lat) < 60) msg('FALLASTE EL ARO', 2);
  }
  if (GSIDE == 0 || abs(side) < 25 || sg == GSIDE) GSIDE = sg;
  for (let i = 0; i < NBN; i++) {
    const o = i * 4; if (!BN[o + 3]) continue;
    const dx = wr(JX - BN[o]), dy = wr(JY - BN[o + 1]), dz = ALT - BN[o + 2];
    if (dx * dx + dy * dy + dz * dz * .36 < 70) {
      BN[o + 3] = 0; CHAIN++; CHT = 6;
      if (!DEMO) { SCORE += 100 * MULT; }
      DEMO || tone(700 + min(CHAIN, 20) * 40, 1400 + min(CHAIN, 20) * 80, .09, 'square', .12);
    }
  }
  if (ALT - G0 < 12) {
    LOWT += dt; LOWC += G0 ? dt : 0;
    if (!DEMO) SCORE += dt * (G0 ? 90 : 25) * MULT;
    if (LOWC > 2) { LOWC = 0; CHAIN++; CHT = 6; if (!DEMO) msg('RASANTE +COMBO', 3); }
  } else { LOWT = 0; LOWC = 0; }
  CHT -= dt; if (CHT <= 0) CHAIN = 0;
  MULT = min(9, 1 + (CHAIN / 4 | 0));
  if (!DEMO && LEVEL >= 2) {
    BIRDT -= dt;
    if (BIRDT <= 0) {
      BIRDT = max(5, 12 - LEVEL * .5) + random() * 4;
      const off = (random() - .5) * 50, fx = JX + c * 220 - s * off, fy = JY + s * 220 + c * off, vx = -c * 22, vy = -s * 22, fh = clamp(ALT + (random() - .5) * 10, gh(fx, fy) + 8, 110);
      for (let k = 0, j = 0; k < NBD && j < 7; k++) {
        const o = k * 6; if (BD[o + 5] > 0) continue;
        const r = (j + 1 >> 1) * (j & 1 ? 1 : -1);
        BD.set([wp(fx + c * abs(r) * 6 - s * r * 7), wp(fy + s * abs(r) * 6 + c * r * 7), fh + (random() - .5) * 4, vx, vy, 16], o); j++;
      }
      if (!DEMO) msg('GAVIOTAS!', 6);
    }
  }
}

function autopilot(dt) {
  const tx = wr(GX - JX), ty = wr(GY - JY), d = hypot(tx, ty), dA = wrapA(atan2(ty, tx) - JA);
  const c = cos(JA), s = sin(JA);
  let th = GA;
  for (let k = 15; k < 100; k += 25) th = max(th, gh(JX + c * k, JY + s * k) + 10);
  step(dt, dA < -.08, dA > .08, ALT < th - 2, ALT > th + 2, d > 160 && BOOST > .4, random() < .002);
}

function blit(cv, x0, y0) {
  const s = SC, iw = W3 / s, ih = H3 / s;
  for (let sy = wp(y0), dy = 0; dy < ih - .01; sy = 0) {
    const ch = min(ih - dy, N - sy);
    for (let sx = wp(x0), dx = 0; dx < iw - .01; sx = 0) { const cw = min(iw - dx, N - sx); OG.drawImage(cv, sx, sy, cw, ch, round(dx * s), round(dy * s), round(cw * s), round(ch * s)); dx += cw; }
    dy += ch;
  }
}
const P = (x, y, h) => { const k = ZC / (ZC - h) * SC; PX = CX + wr(x - JX) * k; PY = CY + wr(y - JY) * k; PK = k; return 1; };
function line(g, ax, ay, bx, by, w) {
  if (ax < 0 && bx < 0 || ay < 0 && by < 0 || ax > W3 && bx > W3 || ay > H3 && by > H3) return;
  const n = ceil(max(abs(bx - ax), abs(by - ay))); if (n > 120) return;
  for (let k = 0; k <= n; k++) { const t = n ? k / n : 0; g.fillRect(round(ax + (bx - ax) * t), round(ay + (by - ay) * t), w, w); }
}
function trails(g, pj) {
  g.fillStyle = '#fff';
  for (let b = 0; b < 4; b++) {
    g.globalAlpha = TA[b];
    for (let j = 1; j < TCN; j++) {
      const o = (TH - 1 - j + TN) % TN * 7, q = (TH - j + TN) % TN * 7;
      if (min(3, (TT - TR[o + 6]) / 1.6 | 0) != b || TR[q + 6] - TR[o + 6] > .2) continue;
      for (let e = 0; e < 6; e += 3) if (pj(TR[o + e], TR[o + e + 1], TR[o + e + 2])) { const ax = PX, ay = PY, w = PK > 9 ? 2 : 1; if (pj(TR[q + e], TR[q + e + 1], TR[q + e + 2])) line(g, ax, ay, PX, PY, w); }
    }
  }
  g.globalAlpha = 1;
}
function ring(g, ov, front) {
  const ok = abs(ALT - GA) < GR * .7, lx = -GDY, ly = GDX;
  for (let p = 0; p < 2; p++) for (let i = 0; i < 48; i++) {
    const t = i / 48 * TAU, a = cos(t) * GR, b = sin(t) * GR;
    let z, y;
    if (ov) { if (GA + b > ALT != front) continue; P(GX + lx * a, GY + ly * a, GA + b); z = max(2, PK * 2.6 + 1.5 | 0); y = PY - b * .75 * PK; }
    else { if (!p3(GX + lx * a, GY + ly * a, GA + b) || PZ > D3 || PZ < 5 || PZ < 30 != front) continue; z = min(9, max(2, PK * 2.2 | 0)); y = PY; }
    g.fillStyle = p ? (i >> 2 & 1) ? '#fff8e8' : ok ? '#4dff6a' : '#ff6a1a' : '#10121e';
    const e = 1 - p; g.fillRect(PX - z / 2 - e | 0, y - z / 2 - e | 0, z + e * 2, z + e * 2);
  }
}
function bananas(g, ov, front) {
  for (let i = 0; i < NBN; i++) {
    const o = i * 4; if (!BN[o + 3]) continue;
    const h = BN[o + 2], dz = h - ALT; let s;
    if (ov) { if (h > ALT != front) continue; P(BN[o], BN[o + 1], h + sin(TT * 3 + i) * 1.2); s = PK; if (PX < -10 || PX > W3 + 10 || PY < -10 || PY > H3 + 10) continue; }
    else { if (!p3(BN[o], BN[o + 1], h) || PZ > 300 || PZ < 7 || PZ < 30 != front) continue; s = min(3, PK * .7); }
    const x = PX | 0, y = PY | 0;
    if (abs(dz) < BTOL) { g.globalAlpha = .45; disc(g, x, y, (ov ? 6 : 4) * s + 1 | 0, '#4dff6a'); g.globalAlpha = 1; }
    else {
      const u = dz > 0 ? -1 : 1, ty = y + u * (5 * s + 4 | 0);
      g.fillStyle = '#10121e'; g.fillRect(x - 3, u < 0 ? ty - 1 : ty - 3, 7, 5);
      g.fillStyle = '#ff8a2a'; for (let k = 0; k < 3; k++) g.fillRect(x - k, ty - u * k, k * 2 + 1, 1);
    }
    const cs = cos(TT * 4 + i) * s; g.setTransform(abs(cs) < .3 * s ? .3 * s : cs, 0, 0, s, PX, PY); g.drawImage(BANS, -5, -5);
    g.setTransform(1, 0, 0, 1, 0, 0);
  }
}
function cloudOv(i) {
  const g = OG, o = i * 4; P(CL[o], CL[o + 1], CL[o + 2]);
  const w = 72 * PK, h = 56 * PK, x = PX - w / 2, y = PY - h / 2;
  if (x > W3 || y > H3 || x + w < 0 || y + h < 0) return;
  g.globalAlpha = CL[o + 2] > ALT && CX > x + w * .15 && CX < x + w * .85 && CY > y + h * .2 && CY < y + h * .8 ? .45 : 1;
  g.drawImage(CLD[CL[o + 3]], x | 0, y | 0, w | 0, h | 0);
  g.globalAlpha = 1;
}
function drawOver() {
  const g = OG;
  SC = ZS / 3; CX = W3 / 2; CY = H3 / 2; ZC = ALT + HC;
  const X0 = JX - CX / SC, Y0 = JY - CY / SC;
  g.setTransform(1, 0, 0, 1, 0, 0); g.globalAlpha = 1;
  blit(MAPC, X0, Y0);
  for (let k = 0; k < 3; k++) { const ph = (TT * .3 + k / 3) % 1; g.globalAlpha = sin(ph * PI) * .9; blit(WAV[k], X0 - (ph * 6 | 0), Y0); }
  g.globalAlpha = .5;
  for (let i = 0; i < NC; i++) { const o = i * 4, h = CL[o + 2]; P(CL[o] + h * SUNX, CL[o + 1] + h * SUNY, 0); if (PX > -50 && PX < W3 + 50 && PY > -40 && PY < H3 + 40) g.drawImage(CSH[CL[o + 3]], PX - 36 * SC | 0, PY - 28 * SC | 0, 72 * SC | 0, 56 * SC | 0); }
  g.globalAlpha = 1;
  g.fillStyle = '#0a1e44';
  const lx = -GDY, ly = GDX;
  for (let i = 0; i < 32; i++) { const t = i / 32 * TAU, a = cos(t) * GR, h = GA + sin(t) * GR; P(GX + lx * a + h * SUNX, GY + ly * a + h * SUNY, 0); g.fillRect(PX | 0, PY | 0, 2, 2); }
  for (let i = 0; i < NBN; i++) { const o = i * 4; if (!BN[o + 3]) continue; const h = BN[o + 2] - gh(BN[o], BN[o + 1]); P(BN[o] + h * SUNX, BN[o + 1] + h * SUNY, 0); g.fillRect(PX - 2 | 0, PY | 0, 4, 2); }
  for (let i = 0; i < NBD; i++) { const o = i * 6; if (BD[o + 5] <= 0) continue; const h = BD[o + 2]; P(BD[o] + h * SUNX, BD[o + 1] + h * SUNY, 0); g.fillRect(PX - 2 | 0, PY | 0, 4, 1); }
  const f = (round(ROLL / TAU * NF) % NF + NF) % NF, c = cos(JA), s = sin(JA), blink = SAFE > 0 && (TT * 14 | 0) % 2;
  if (DEAD <= 0) {
    const h = ALT - G0, ss = max(.6, 1 - h / 260);
    P(JX + h * SUNX, JY + h * SUNY, 0);
    g.globalAlpha = .5; g.setTransform(c * ss, s * ss, -s * ss, c * ss, PX, PY); g.drawImage(JSH, f * JG, 0, JG, JG, -16, -16, JG, JG);
    g.setTransform(1, 0, 0, 1, 0, 0); g.globalAlpha = 1;
  }
  let ci = 0;
  const cl = a => { for (; ci < NC && CL[ci * 4 + 2] < a; ci++) cloudOv(ci); };
  cl(min(GA - GR, ALT));
  g.fillStyle = '#fff';
  if (DEAD <= 0 && ALT < 9 && !G0) for (let k = 0; k < 14; k++) { const d = 4 + random() * 15, w = (random() - .5) * (3 + d * .6); g.fillRect(CX - c * d - s * w | 0, CY - s * d + c * w | 0, 1 + (random() * 2 | 0), 1); }
  trails(g, P);
  ring(g, 1, 0);
  for (let i = 0; i < LH.length; i += 2) {
    P(LH[i], LH[i + 1], 0);
    if (PX < -10 || PX > W3 + 10 || PY < -30 || PY > H3 + 10) continue;
    for (let l = 0; l < 16; l++) { g.fillStyle = l > 14 ? ((TT * 2 | 0) % 2 ? '#fff6a0' : '#a08020') : l > 13 ? '#22242a' : l < 2 ? '#6b6f78' : (l >> 1 & 1) ? '#d83a2a' : '#f4f4f0'; g.fillRect(PX - 1 | 0, PY - 1 - l * .8 | 0, 3, 3); }
  }
  bananas(g, 1, 0);
  for (let i = 0; i < NBD; i++) {
    const o = i * 6; if (BD[o + 5] <= 0) continue;
    P(BD[o], BD[o + 1], BD[o + 2]); const x = PX | 0, y = PY | 0, fl = (TT * 7 + i | 0) % 2;
    g.fillStyle = '#20242c'; g.fillRect(x - 5, y - 1 - fl, 11, 3 + fl);
    g.fillStyle = '#ffffff'; g.fillRect(x - 1, y - 1, 3, 2);
    if (fl) { g.fillRect(x - 4, y - 1, 3, 1); g.fillRect(x + 2, y - 1, 3, 1); g.fillStyle = '#7a8090'; g.fillRect(x - 5, y - 2, 1, 1); g.fillRect(x + 5, y - 2, 1, 1); }
    else { g.fillRect(x - 4, y, 9, 1); g.fillStyle = '#7a8090'; g.fillRect(x - 5, y, 1, 1); g.fillRect(x + 5, y, 1, 1); }
    g.fillStyle = '#ff9a1a'; g.fillRect(x, y + 1, 1, 1);
  }
  parts(g, P, 4, 2);
  cl(ALT);
  if (DEAD <= 0 && !blink) {
    const L = JLAY[f], hc = JG / 2 - .5;
    g.globalAlpha = .85;
    for (let d = 0; d < 4; d++) { g.setTransform(c, s, -s, c, CX + (d < 2 ? d * 2 - 1 : 0), CY + (d > 1 ? d * 2 - 5 : 0)); g.drawImage(JSH, f * JG, 0, JG, JG, -16, -16, JG, JG); }
    g.globalAlpha = 1;
    for (let l = L[0]; l <= L[1]; l++) {
      g.setTransform(c, s, -s, c, CX, CY - (l - hc) * LO);
      g.drawImage(JET, f * JG, l * JG, JG, JG, -16, -16, JG, JG);
      if (l == 15) { const len = (THR ? 11 : 5) * (.75 + random() * .5), fr = TT * 20 % 3 | 0; g.drawImage(FLM, fr * 10, 0, 10, 3, FLX - len, -1.5, len, 3); }
    }
    g.setTransform(1, 0, 0, 1, 0, 0);
  }
  ring(g, 1, 1);
  bananas(g, 1, 1);
  cl(999);
  OVT.refresh();
}
function parts(g, pj, mz, f) {
  for (let i = 0; i < NPT; i++) {
    const o = i * 7, l = PA[o + 6]; if (l <= 0 || !pj(PA[o], PA[o + 1], PA[o + 2])) continue;
    g.fillStyle = l > 1.1 ? '#fff4b0' : l > .8 ? '#ffb020' : l > .5 ? '#ff5a1a' : '#555a66';
    const z = min(mz, max(1, PK * f * (l > .6 ? 1.5 : 1) | 0)); g.fillRect(PX - z / 2 | 0, PY - z / 2 | 0, z, z);
  }
}

const p3 = (x, y, h) => {
  const dx = wr(x - C3x), dy = wr(y - C3y), z = dx * C3ca + dy * C3sa;
  if (z < 2) { PK = 0; return 0; }
  const xr = (-dx * C3sa + dy * C3ca) / z * FOC;
  PX = W3 / 2 + xr; PY = C3hor + (C3alt - h) * FOC / z - xr * C3tr; PK = FOC / z; PZ = z; return 1;
};
function vox(cxp, cyp, calt, ca, sa, hor, tr, cock) {
  const U = U3, C = COL, V = VR, fk = 290 / (D3 * D3);
  for (let x = 0; x < W3; x++) {
    const r = (x - W3 / 2) / FOC, dx = ca - sa * r, dy = sa + ca * r, hx0 = hor - (x - W3 / 2) * tr;
    let yb = cock ? PT[x] : H3, z = 3, dz = .3;
    while (z < D3 && yb > 0) {
      const i = ((cyp + dy * z) & M) * N + ((cxp + dx * z) & M), y = hx0 + (calt - V[i]) * FOC / z | 0;
      if (y < yb) {
        let c = C[i]; const a = z * z * fk | 0;
        const y0 = y < 0 ? 0 : y;
        if (c >>> 24 < 255) for (let p = y0 * W3 + x, yy = y0; yy < yb; yy++, p += W3) { const l = 15 - (yy - y) * z / FOC * 16 / LHH | 0; U[p] = LHC[l < 0 ? 16 : l]; }
        else {
          if (a > 0) { const b = a > 255 ? 255 : a, q = 256 - b; c = 0xff000000 | ((c >> 16 & 255) * q + FB * b >> 8) << 16 | ((c >> 8 & 255) * q + FG * b >> 8) << 8 | ((c & 255) * q + FR * b >> 8); }
          for (let p = y0 * W3 + x, e = yb * W3; p < e; p += W3) U[p] = c;
        }
        yb = y0;
      }
      z += dz; dz += .006;
    }
    const o = (hx0 | 0) - H3;
    for (let p = x, yy = 0; yy < yb; yy++, p += W3) { const k = yy - o; U[p] = SKY[k < 0 ? 0 : k >= SKN ? SKN - 1 : k]; }
  }
}
function draw3D(cock) {
  const g = P3G;
  let rl = clamp(BANK, -.9, .9);
  if (cock) { C3x = JX; C3y = JY; C3alt = ALT + 2; CAMA = JA; C3hor = H3 * .42 + PITCH * 30; }
  else {
    C3x = JX - cos(CAMA) * 30; C3y = JY - sin(CAMA) * 30; C3alt = max(CAMALT, gh(C3x, C3y) + 4); C3hor = H3 * .3 + PITCH * 16; rl *= .35;
  }
  C3ca = cos(CAMA); C3sa = sin(CAMA); C3tr = tan(rl);
  vox(C3x, C3y, C3alt, C3ca, C3sa, C3hor, C3tr, cock);
  g.putImageData(P3D, 0, 0);
  g.setTransform(1, 0, 0, 1, 0, 0); g.globalAlpha = 1;
  let n = 0;
  for (let i = 0; i < NC; i++) { const o = i * 4; if (p3(CL[o], CL[o + 1], CL[o + 2]) && PZ < D3 && PZ > 9 && PX > -120 && PX < W3 + 120) { let j = n++; while (j > 0 && CZ[j - 1] < PZ) { CZ[j] = CZ[j - 1]; CI[j] = CI[j - 1]; j--; } CZ[j] = PZ; CI[j] = i; } }
  const bb = j => { const o = CI[j] * 4; p3(CL[o], CL[o + 1], CL[o + 2]); const s = PK * 1.1, w = 72 * s, h = 56 * s * .7; g.globalAlpha = min(1, (D3 - PZ) / 90); g.drawImage(CSD[CL[o + 3]], PX - w / 2 | 0, PY - h / 2 | 0, w | 0, h | 0); };
  let j = 0;
  for (; j < n && CZ[j] > 34; j++) bb(j);
  g.globalAlpha = 1;
  ring(g, 0, 0);
  bananas(g, 0, 0);
  for (let i = 0; i < NBD; i++) { const o = i * 6; if (BD[o + 5] <= 0 || !p3(BD[o], BD[o + 1], BD[o + 2])) continue; const w = min(24, max(3, PK * 5 | 0)), hh = max(1, w / 5 | 0), fl = (TT * 7 + i | 0) % 2; g.fillStyle = '#f4f4f4'; g.fillRect(PX - w / 2 | 0, PY - (fl ? hh : 0) | 0, w, hh); g.fillStyle = '#20242c'; g.fillRect(PX - hh | 0, PY | 0, hh * 2, hh); }
  trails(g, p3);
  parts(g, p3, 6, .8);
  if (!cock && DEAD <= 0 && !(SAFE > 0 && (TT * 14 | 0) % 2) && p3(JX, JY, ALT)) {
    const r = ROLL - rl, c = cos(r) * 2, s = sin(r) * 2;
    g.setTransform(c, s, -s, c, PX, PY); g.drawImage(JREAR, -16, -26);
    const q = (THR ? .9 : .6) * (.8 + random() * .4), fr = TT * 20 % 3 | 0;
    g.drawImage(FLR, fr * 7, 0, 7, 7, -3.5 * q, -3.5 * q, 7 * q, 7 * q);
    g.setTransform(1, 0, 0, 1, 0, 0);
  }
  ring(g, 0, 1);
  bananas(g, 0, 1);
  for (; j < n; j++) bb(j);
  g.globalAlpha = 1;
  if (cock) cockpit();
  P3T.refresh();
}
function cockpit() {
  const g = P3G;
  g.drawImage(PANEL, 0, 0);
  R32.fill(hx(0x06281a));
  const c = cos(JA), s = sin(JA), k = 7;
  for (let v = -19; v <= 19; v += 2) for (let u = -28; u <= 28; u += 2) {
    const h = gh(JX - c * v * k - s * u * k, JY - s * v * k + c * u * k);
    if (h) { const cc = GRN[min(3, h / 14 | 0)], p = (21 + v) * 58 + 29 + u; R32[p] = R32[p + 1] = R32[p + 58] = R32[p + 59] = cc; }
  }
  const sw = TT * 3 % TAU;
  for (let r = 2; r < 26; r++) { const x = 29 + round(cos(sw) * r), y = 21 + round(sin(sw) * r * .75); if (x >= 0 && x < 58 && y >= 0 && y < 40) R32[y * 58 + x] = hx(0x6cff9a); }
  const gx = wr(GX - JX), gy = wr(GY - JY);
  let u = (-gx * s + gy * c) / k, v = -(gx * c + gy * s) / k;
  const m = max(abs(u) / 27, abs(v) / 19); if (m > 1) { u /= m; v /= m; }
  if ((TT * 4 | 0) % 2) for (let a = -1; a <= 1; a++) for (let b = -1; b <= 1; b++) { const p = (21 + round(v) + b) * 58 + 29 + round(u) + a; if (p >= 0 && p < 2320) R32[p] = hx(0xffd21e); }
  R32[21 * 58 + 29] = R32[20 * 58 + 29] = hx(0xffffff);
  cx2(RADC).putImageData(RADD, 0, 0); g.drawImage(RADC, 13, 153);
  const rl = clamp(BANK, -.9, .9), sr = sin(rl), cr = cos(rl), hp = PITCH * 10;
  B32.fill(0);
  for (let y = -16; y <= 16; y++) for (let x = -16; x <= 16; x++) {
    if (x * x + y * y > 272) continue;
    const vr = x * sr + y * cr, ur = x * cr - y * sr;
    B32[(y + 16) * 33 + x + 16] = abs(vr - hp) < .8 || abs(vr - hp + 7) < .5 && abs(ur) < 5 || abs(vr - hp - 7) < .5 && abs(ur) < 5 ? hx(0xffffff) : vr < hp ? (vr < hp - 9 ? hx(0x2f7ed0) : hx(0x4aa0ec)) : hx(0x9a6332);
  }
  cx2(BALLC).putImageData(BALD, 0, 0); g.drawImage(BALLC, 117, 154);
  g.fillStyle = '#ffd21e'; g.fillRect(126, 170, 5, 1); g.fillRect(136, 170, 5, 1); g.fillRect(133, 169, 1, 3);
  g.fillStyle = '#ff6a1a';
  for (let k = 0; k < 2; k++) { const t = -3.9 + clamp(k ? ALT / 125 : (SPD - 30) / 60, 0, 1) * 4.6; for (let r = 0; r < 9; r++) g.fillRect(97 + k * 72 + round(cos(t) * r), 170 + round(sin(t) * r), 1, 1); }
  LT[0] = THR; LT[1] = RCD <= 0; LT[2] = LOWT > 0; LT[3] = WARN > 0 || DEAD > 0; LT[4] = MULT > 1;
  for (let i = 0; i < 5; i++) if (LT[i] && (i != 3 || (TT * 6 | 0) % 2)) { g.fillStyle = LC[i]; g.fillRect(112 + i * 9, 141, 7, 3); }
}

function T(s, x, y, c, z, al, ns) {
  s = '' + s; c = c || 0; z = z || 1;
  const w = s.length * 4 * z - z, o = z > 2 ? 2 : 1;
  x = (al ? al > 1 ? x - w : x - w / 2 : x) | 0; y |= 0;
  for (let k = ns ? 1 : 0; k < 2; k++) for (let i = 0; i < s.length; i++) {
    const gi = FCH.indexOf(s[i]); if (gi < 0 || gi == 10) continue;
    HG.drawImage(FONT, gi * 4, (k ? c : 7) * 6, 3, 5, x + i * 4 * z + (k ? 0 : o), y + (k ? 0 : o), 3 * z, 5 * z);
  }
}
const box = (x, y, w, h, a) => { HG.globalAlpha = a; HG.fillStyle = '#0a1028'; HG.fillRect(x, y, w, h); HG.globalAlpha = 1; };
const arrow = (x, y, a, k) => HG.drawImage(ARW, (round(a / TAU * 16) & 15) * 17, k * 17, 17, 17, x - 8 | 0, y - 8 | 0, 17, 17);
function gameHud() {
  const v = VIEW, bl = (TT * 4 | 0) % 2, Y = '#ffd21e';
  if (v < 2) {
    T('PUNTOS', 8, 6, 6); T(SCORE | 0, 8, 13, 0, 2);
    for (let i = 0; i < LIVES; i++) HG.drawImage(LIFE, 382 - i * 13, 6);
    if (MULT > 1) T('COMBO X' + MULT, 392, 20, 2, 2, 2);
    T('AROS ' + GATES, 392, 34, 6, 1, 2);
    box(8, 70, 9, 150, .45);
    HG.fillStyle = WARN > 0 && bl ? '#ff3a2a' : '#6a5a3a'; const gtop = 220 - min(150, GW * 1.2); HG.fillRect(9, gtop, 7, 220 - gtop);
    HG.fillStyle = abs(ALT - GA) < GR * .7 ? '#4dff6a' : '#ff6a1a'; HG.fillRect(8, 220 - GA * 1.2 - 2, 9, 4);
    HG.fillStyle = Y; HG.fillRect(17, 220 - ALT * 1.2 - 1, 4, 3); HG.fillRect(5, 220 - ALT * 1.2, 3, 1);
    T('ALT', 8, 62, 6); T(ALT | 0, 8, 224, 0);
    T('TURBO', 8, 254, 6); box(8, 262, 62, 6, .5); HG.fillStyle = THR ? '#fff2a0' : '#ff8a1a'; HG.fillRect(9, 263, BOOST * 60, 4);
    T(RCD <= 0 ? 'TONEL LISTO' : 'TONEL ...', 80, 262, RCD <= 0 ? 5 : 6);
  } else {
    T(SCORE | 0, 325, 232, 8, 1, 1); T('ALT ' + (ALT | 0), 325, 242, 8, 1, 1); T('VEL ' + (SPD * 9 | 0), 325, 252, 8, 1, 1); T('X' + MULT + ' VIDAS ' + LIVES, 325, 262, 8, 1, 1);
    T('AROS ' + GATES, 325, 276, 5, 1, 1);
  }
  const ty = v == 2 ? 22 : 6;
  T('TIEMPO', 200, ty, 6, 1, 1); T(ceil(TIME), 200, ty + 7, TIME < 10 ? (bl ? 4 : 0) : 1, 3, 1);
  const gx = wr(GX - JX), gy = wr(GY - JY), d = hypot(gx, gy), dh = GA - ALT, ok = abs(dh) <= GR * .7, sa = v ? wrapA(atan2(gy, gx) - CAMA) - PI / 2 : atan2(gy, gx);
  arrow(200, ty + 36, sa, 0);
  T((d | 0) + 'M', 200, ty + 47, 0, 1, 1);
  let jx = 200, jy = 150;
  if (v == 1 && p3(JX, JY, ALT)) { jx = PX * 1.5; jy = PY * 1.5; }
  if (v == 2) jy = 140;
  if (ok) T('ALTURA OK', 200, ty + 56, 5, 1, 1);
  if (WARN > 0) { if (bl) T('SUBE!', jx, jy + 26, 4, 2, 1); }
  else if (!ok) T(dh > 0 ? 'SUBE ^' : 'BAJA v', jx, jy + 26, 2, 2, 1);
  if (v ? p3(GX, GY, GA) && PX > 0 && PX < W3 && PY > 0 && PY < H3 : P(GX, GY, GA) && PX > 0 && PX < W3 && PY > 0 && PY < H3) {
    const x = PX * 1.5, y = PY * 1.5, r = max(6, PK * GR * 1.5);
    HG.fillStyle = bl ? Y : ok ? '#4dff6a' : '#ff6a1a';
    for (let k = 0; k < 4; k++) { const sx = k & 1 ? 1 : -1, sy = k & 2 ? 1 : -1, cx = x + sx * r, cy = y + sy * r; HG.fillRect(sx > 0 ? cx - 4 : cx, cy, 5, 2); HG.fillRect(cx, sy > 0 ? cy - 4 : cy, 2, 5); }
  } else arrow(jx + cos(sa) * 46, jy + sin(sa) * 46, sa, ok ? 1 : 2);
  if (LOWT > .3 && bl) T('VUELO RASANTE', 200, v == 2 ? 120 : 236, 5, 1, 1);
  if (hypot(WX, WY) > 4) { T('RAFAGA', 330, 46, 3, 1, 1); arrow(330, 62, atan2(WY, WX) - (v ? CAMA + PI / 2 : 0), 0); }
}
function table(y) {
  T('MEJORES PILOTOS', 200, y, 1, 2, 1);
  for (let i = 0; i < 5; i++) {
    const r = HS[i], c = i == LASTI ? 1 : 0, yy = y + 22 + i * 12;
    T((i + 1) + '.', 140, yy, 6); T(r ? r.n : '---', 160, yy, c); T(r ? r.s : 0, 260, yy, c, 1, 2);
  }
}
const HELP = 'PALANCA: VIRA/SUBE/BAJA  B1 TURBO  B2 TONEL  B3 VISTA';
function hud() {
  HG.setTransform(1, 0, 0, 1, 0, 0); HG.clearRect(0, 0, 400, 300);
  const bl = (TT * 2.5 | 0) % 2;
  if (MODE == 1) gameHud();
  if (MODE == 0) {
    const ck = VIEW == 2, oy = ck ? -72 : 0;
    box(0, 0, 400, 300, .18);
    for (let d = 6; d >= 0; d--) { const c = d > 5 ? 7 : d ? 2 : 1; T('VUELO', 200, 18 + d, c, 7, 1, 1); T('AUSTRAL', 200, 60 + d, c, 7, 1, 1); }
    ck || T('ARCADE DE VUELO SOBRE LAS ISLAS DEL SUR', 200, 108, 0, 1, 1);
    if (TSHOW || (MT / 7 | 0) % 2) { box(120, 172 + oy, 160, 92, .55); table(178 + oy); }
    else { if (bl) T('PRESS START', 200, 200 + oy, 0, 2, 1); box(70, 226 + oy, 260, 26, .4); T('CRUZA AROS - JUNTA PLATANOS - VUELA BAJO', 200, 230 + oy, 3, 1, 1); T('B1 TURBO  B2 TONEL  B3 VISTA', 200, 241 + oy, 6, 1, 1); }
    if (MT > 7 && TSHOW) TSHOW = 0;
  }
  if (MODE == 2) {
    box(70, 90, 260, 90, .6);
    T('FIN DEL VUELO', 200, 100, 4, 3, 1); T(GOR ? 'SIN VIDAS' : 'SIN TIEMPO', 200, 126, 6, 1, 1);
    T('PUNTAJE', 200, 142, 6, 1, 1); T(SCORE, 200, 152, 1, 3, 1);
  }
  if (MODE == 3) {
    box(70, 60, 260, 170, .6);
    T('NUEVO RECORD!', 200, 70, 1, 3, 1); T(SCORE, 200, 96, 0, 2, 1); T('ESCRIBE TUS INICIALES', 200, 118, 6, 1, 1);
    for (let i = 0; i < 3; i++) { const x = 160 + i * 40; T(AL[NM[i]], x, 134, i == NP ? 1 : 0, 6, 1); if (i == NP && bl) { HG.fillStyle = '#ffd21e'; HG.fillRect(x - 10, 168, 20, 3); } }
    T('ARRIBA/ABAJO LETRA  IZQ/DER MOVER', 200, 184, 6, 1, 1); T('B1 O START CONFIRMA', 200, 194, 6, 1, 1); T(max(0, 30 - MT) | 0, 200, 210, 6, 1, 1);
  }
  let my = 999;
  for (const m of MSG) if (m[1] > 0) { my = min(96 - (1.6 - m[1]) * 18, my - 15); T(m[0], 200, my, m[2], 2, 1); }
  if (MODE < 2 && VIEW < 2) { box(0, 286, 400, 14, .45); T(HELP, 200, 290, 0, 1, 1); }
  if (MODE == 1 && VIEW == 2) T(HELP, 200, 6, 6, 1, 1);
  HT.refresh();
}

function frame(dt) {
  TT += dt; MT += dt; SHK = max(0, SHK - dt);
  for (const m of MSG) m[1] -= dt;
  if (PR[I3]) { VIEW = (VIEW + 1) % 3; VLOCK = 1; tone(440, 660, .06, 0, .1); }
  if (MODE == 0) {
    if (!VLOCK) VIEW = VSEQ[MT / 9 % 5 | 0];
    autopilot(dt);
    if (PR[IS] || PR[I1]) startGame();
  } else if (MODE == 1) {
    PLAYT += dt; LEVEL = max(GATES / 3 | 0, PLAYT / 40 | 0);
    step(dt, HD[IL], HD[IR], HD[IU], HD[ID], HD[I1], PR[I2]);
    if (MODE == 1) {
      TIME -= dt;
      if (TIME < 10 && ceil(TIME) != BEEP) { BEEP = ceil(TIME); tone(990, 990, .06, 0, .1); }
      if (TIME <= 0) { TIME = 0; gameOver(0); }
    }
  } else if (MODE == 2) {
    autopilot(dt);
    if (MT > 3.5 || MT > 1.5 && (PR[I1] || PR[IS])) {
      if (SCORE > 0 && (HS.length < 5 || SCORE > HS[HS.length - 1].s)) { MODE = 3; MT = 0; NM = [0, 0, 0]; NP = 0; }
      else { MODE = 0; MT = 0; VLOCK = 0; TSHOW = 1; }
    }
  } else {
    autopilot(dt);
    const ud = PR[IU] ? 1 : PR[ID] ? -1 : HD[IU] ? 1 : HD[ID] ? -1 : 0;
    if (PR[IU] || PR[ID]) { NM[NP] = (NM[NP] + ud + 37) % 37; RH = 0; RN = .4; tone(600, 600, .04, 0, .08); }
    else if (ud) { RH += dt; if (RH > RN) { RN += .11; NM[NP] = (NM[NP] + ud + 37) % 37; } }
    if (PR[IL]) NP = max(0, NP - 1);
    if (PR[IR]) NP = min(2, NP + 1);
    if (PR[I1] || PR[IS] || MT > 30) {
      if (NP < 2 && MT <= 30) { NP++; tone(800, 800, .05, 0, .1); }
      else {
        let n = NM.map(i => AL[i]).join('');
        if (!n.trim()) n = 'AAA';
        const r = { n, s: SCORE };
        HS.push(r); HS = vhs(HS); LASTI = HS.findIndex(q => q.n == n && q.s == SCORE); hsSave();
        MODE = 0; MT = 0; VLOCK = 0; TSHOW = 1; tone(523, 1046, .3, 0, .15);
      }
    }
  }
  CAMA += wrapA(JA - CAMA) * min(1, dt * 2.6);
  CAMALT += (ALT + 9 - CAMALT) * min(1, dt * 3);
  ZS += (min(3.4, max(2, FZ / (ALT + HC))) - ZS) * min(1, dt * 4);
  if (AC && EG) {
    music();
    const t = AC.currentTime;
    EF.frequency.setTargetAtTime(220 + SPD * 6 + THR * 700, t, .15);
    EO.frequency.setTargetAtTime(36 + SPD * .7 + THR * 30, t, .15);
    EG.gain.setTargetAtTime(DEAD > 0 || MODE > 1 ? .02 : MODE == 1 ? .2 : .06, t, .2);
  }
  const sx = SHK > 0 ? (random() - .5) * SHK * 16 : 0, sy = SHK > 0 ? (random() - .5) * SHK * 16 : 0;
  OVI.setVisible(VIEW == 0).setPosition(sx, sy); P3I.setVisible(VIEW > 0).setPosition(sx, sy);
  if (VIEW == 0) drawOver(); else draw3D(VIEW == 2);
  hud();
}

function create() {
  S = this;
  genWorld(); bakeJet(); bakeMisc(); bakeSky(); bakePanel(); placeClouds();
  OVT = S.textures.createCanvas('ov', W3, H3); OG = OVT.context; OG.imageSmoothingEnabled = false;
  OVI = S.add.image(0, 0, 'ov').setOrigin(0).setScale(3);
  P3T = S.textures.createCanvas('p3', W3, H3); P3G = P3T.context; P3G.imageSmoothingEnabled = false;
  P3D = P3G.createImageData(W3, H3); U3 = new Uint32Array(P3D.data.buffer);
  P3I = S.add.image(0, 0, 'p3').setOrigin(0).setScale(3);
  HT = S.textures.createCanvas('hud', 400, 300); HG = HT.context; HG.imageSmoothingEnabled = false;
  HUI = S.add.image(0, 0, 'hud').setOrigin(0).setScale(2);
  RADD = cx2(RADC).createImageData(58, 40); R32 = new Uint32Array(RADD.data.buffer);
  BALD = cx2(BALLC).createImageData(33, 33); B32 = new Uint32Array(BALD.data.buffer);
  reset(1);
  hsLoad();
}
function update(_, dms) {
  const dt = min(dms, 50) / 1000;
  PR.set(PQ); PQ.fill(0);
  try { frame(dt); } catch (e) { setTimeout(() => { throw e; }); }
}

new Phaser.Game({
  type: Phaser.CANVAS, width: 800, height: 600, parent: 'game-root', backgroundColor: '#000', pixelArt: true, banner: false,
  audio: { noAudio: true },
  scale: { mode: Phaser.Scale.FIT, autoCenter: Phaser.Scale.CENTER_BOTH },
  scene: { create, update },
});
})();
