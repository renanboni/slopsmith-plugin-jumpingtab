(function () {
    'use strict';

    // ── Constants ─────────────────────────────────────────────
    const AHEAD = 8.0;
    const BEHIND = 1.2;
    const HIT_LINE_FRAC = 0.18;
    const FADE_SECONDS = 1.0;
    const SQUASH_WINDOW_MS = 60;
    const TOP_PAD = 60;           // room for header strip
    const BOTTOM_PAD = 36;        // room for progress bar
    const HIT_ZONE_WIDTH = 56;    // wide glowing strip around hit line
    const EDGE_FADE_FRAC = 0.06;  // % of canvas width to fade at edges
    const NOTE_BASE_R = 14;
    const NOTE_MAX_R = 18;        // max radius at hit line
    const HEADER_H = 36;

    const GUITAR_COLORS = ['#ff6b8b', '#ffa56b', '#ffe66b', '#6bff95', '#6bd5ff', '#c56bff'];
    const BASS_COLORS   = ['#ff6b8b', '#ffe66b', '#6bff95', '#6bd5ff'];

    // ── Pure helpers ──────────────────────────────────────────
    function stringY(s, height, nStrings) {
        const usable = height - TOP_PAD - BOTTOM_PAD;
        const gap = usable / (nStrings - 1);
        return TOP_PAD + s * gap;
    }

    function colorsFor(nStrings) {
        return nStrings === 4 ? BASS_COLORS : GUITAR_COLORS;
    }

    function timeX(t, now, width) {
        const hitX = width * HIT_LINE_FRAC;
        const dt = t - now;
        return hitX + (dt / AHEAD) * (width - hitX);
    }

    function binaryVisibleRange(notes, now) {
        const lo = now - BEHIND;
        const hi = now + AHEAD;
        // first index with t >= lo
        let l = 0, r = notes.length;
        while (l < r) {
            const m = (l + r) >> 1;
            if (notes[m].t < lo) l = m + 1; else r = m;
        }
        const start = l;
        // first index with t > hi
        l = start; r = notes.length;
        while (l < r) {
            const m = (l + r) >> 1;
            if (notes[m].t <= hi) l = m + 1; else r = m;
        }
        return { start, end: l };
    }

    function buildTrajectories(notes) {
        // Group notes by (near-)timestamp, preserving sort order. A group
        // with more than one note is a chord. We emit an arc between every
        // two consecutive groups so the ball always has somewhere to go —
        // chord→chord included. For chord endpoints we use the average
        // string index (float) so the arc visually lands on the centroid
        // of the chord stack rather than one arbitrary string.
        if (notes.length < 2) return [];

        // Server rounds note times to 3 decimal places (ms precision), so
        // chord notes arrive with byte-identical floats. Keep a small
        // epsilon so any rounding drift upstream still groups them.
        const EPS = 1e-4;
        const groups = [];
        let i = 0;
        while (i < notes.length) {
            const t = notes[i].t;
            let j = i;
            while (j < notes.length && Math.abs(notes[j].t - t) < EPS) j++;
            const slice = notes.slice(i, j);
            let sSum = 0;
            for (const n of slice) sSum += n.s;
            groups.push({
                t,
                notes: slice,
                sAvg: sSum / slice.length,
                // Representative fret — used only for logging/debug
                f: slice[0].f,
            });
            i = j;
        }

        const arcs = [];
        for (let k = 0; k < groups.length - 1; k++) {
            const a = groups[k];
            const b = groups[k + 1];
            arcs.push({
                t0: a.t, t1: b.t,
                s0: a.sAvg, f0: a.f,
                s1: b.sAvg, f1: b.f,
            });
        }
        return arcs;
    }

    // Map a numeric bend amount (in semitones) to the label conventionally
    // shown in guitar tablature. 0.5 → ½, 1 → "full", 1.5 → 1½, etc.
    function bendText(bn) {
        if (!bn || bn <= 0) return '';
        if (bn === 0.5) return '\u00BD';
        if (bn === 1) return 'full';
        if (bn === 1.5) return '1\u00BD';
        if (bn === 2) return '2';
        if (bn === 2.5) return '2\u00BD';
        if (bn >= 3) return String(Math.round(bn));
        return bn.toFixed(1);
    }

    function bezierPoint(x0, y0, cx, cy, x1, y1, u) {
        const v = 1 - u;
        return {
            x: v * v * x0 + 2 * v * u * cx + u * u * x1,
            y: v * v * y0 + 2 * v * u * cy + u * u * y1,
        };
    }

    // ── Exports for test harness ──────────────────────────────
    window.__jumpingtab_core = {
        stringY, colorsFor, timeX, binaryVisibleRange, buildTrajectories, bezierPoint,
        AHEAD, BEHIND, HIT_LINE_FRAC,
    };

    // ── WS state ──────────────────────────────────────────────
    const state = {
        filename: null,
        tuning: null,
        notes: [],
        arcs: [],
        techArcs: [],
        techPaired: new Set(),
        beats: [],
        sections: [],
        songInfo: {},
        ready: false,
        ws: null,
    };

    // Build "technique arcs" — pairs of two notes on the same string where
    // the second note has a hammer-on / pull-off / slide flag set. Walks
    // the time-sorted notes array once; for each note with a technique
    // flag, finds the most recent prior note on the same string and emits
    // a pair. Returns {arcs, paired} where `paired` is a Set of note
    // references that belong to any pair — used by drawNotes to skip
    // them (drawTechniquePairs renders them as a fused capsule instead).
    function buildTechniqueArcs(notes) {
        const arcs = [];
        const paired = new Set();
        const lastOnString = new Map();  // string index → last note object
        for (const n of notes) {
            const prev = lastOnString.get(n.s);
            if (prev) {
                let type = null;
                if (n.ho) type = 'h';
                else if (n.po) type = 'p';
                else if (n.sl && n.sl > 0) type = 's';
                if (type) {
                    arcs.push({ t0: prev.t, t1: n.t, s: n.s, type, f0: prev.f, f1: n.f });
                    paired.add(prev);
                    paired.add(n);
                }
            }
            lastOnString.set(n.s, n);
        }
        return { arcs, paired };
    }

    function connect(filename, arrangementIdx) {
        return new Promise((resolve, reject) => {
            // Close any prior socket
            if (state.ws) { try { state.ws.close(); } catch (e) {} state.ws = null; }
            state.filename = filename;
            state.tuning = null;
            state.notes = [];
            state.arcs = [];
            state.techArcs = [];
            state.techPaired = new Set();
            state.beats = [];
            state.sections = [];
            state.songInfo = {};
            state.ready = false;

            const proto = location.protocol === 'https:' ? 'wss:' : 'ws:';
            const qs = (arrangementIdx != null && arrangementIdx >= 0)
                ? `?arrangement=${arrangementIdx}` : '';
            const url = `${proto}//${location.host}/ws/highway/${encodeURIComponent(filename)}${qs}`;
            const ws = new WebSocket(url);
            state.ws = ws;

            let singleNotesCount = 0;
            let chordNotesCount = 0;

            const finalize = () => {
                if (state.ready) return;
                state.notes.sort((a, b) => a.t - b.t);
                state.arcs = buildTrajectories(state.notes);
                const tech = buildTechniqueArcs(state.notes);
                state.techArcs = tech.arcs;
                state.techPaired = tech.paired;
                state.ready = true;
                console.log('[jumpingtab] ready —',
                    singleNotesCount, 'single notes +',
                    chordNotesCount, 'chord notes =',
                    state.notes.length, 'total,',
                    state.techArcs.length, 'technique arcs');
                resolve(state);
            };

            // Identity-gate all handlers: if the user picks a different song
            // before this one finishes loading, state.ws is replaced. Old
            // handlers continue firing — ignore them so they can't mutate
            // the new song's state.
            ws.onmessage = (ev) => {
                if (state.ws !== ws) return;
                let msg;
                try { msg = JSON.parse(ev.data); } catch (e) { return; }
                if (msg.error) { reject(new Error(msg.error)); ws.close(); return; }
                if (msg.type === 'song_info') {
                    state.tuning = msg.tuning || [0,0,0,0,0,0];
                    state.songInfo = {
                        title: msg.title || '',
                        artist: msg.artist || '',
                        arrangement: msg.arrangement || '',
                        duration: msg.duration || 0,
                    };
                    const mode = state.tuning.length === 4 ? 'bass (4)' : 'guitar (6)';
                    console.log('[jumpingtab] arrangement:', msg.arrangement, '— mode:', mode);
                } else if (msg.type === 'sections') {
                    state.sections = msg.data || [];
                } else if (msg.type === 'notes') {
                    // Single (non-chord) notes
                    for (const n of msg.data) state.notes.push(n);
                    singleNotesCount = state.notes.length;
                } else if (msg.type === 'chords') {
                    // Chord events — each chord has its own time and a list of
                    // notes {s, f, sus, ...}. Expand into individual notes by
                    // promoting the chord's time onto every note. Keep the
                    // technique flags (ho, po, sl, bn) so drawTechniqueArcs
                    // and drawBends can find them.
                    for (const c of msg.data) {
                        for (const cn of c.notes) {
                            state.notes.push({
                                t: c.t,
                                s: cn.s,
                                f: cn.f,
                                sus: cn.sus || 0,
                                ho: cn.ho || 0,
                                po: cn.po || 0,
                                sl: cn.sl || -1,
                                bn: cn.bn || 0,
                            });
                            chordNotesCount++;
                        }
                    }
                } else if (msg.type === 'beats') {
                    // Store beats for measure-bar rendering in drawBackground
                    state.beats = msg.data || [];
                } else if (msg.type === 'ready') {
                    // Server has finished streaming notes + chords
                    finalize();
                }
            };
            ws.onerror = () => {
                if (state.ws !== ws) return;
                if (!state.ready) reject(new Error('ws error'));
            };
            ws.onclose = () => {
                if (state.ws !== ws) return;
                if (!state.ready) reject(new Error('ws closed before ready'));
            };
        });
    }

    // ── Canvas lifecycle ─────────────────────────────────────
    let active = false;
    let canvas = null;
    let wrap = null;
    let ctx = null;
    let raf = null;
    let audioEl = null;

    // Player-view Y mapping: low E (highest string index) at top, high e
    // (index 0) at bottom — matches what you see when looking down at your
    // own guitar. Keeps stringY pure (tests untouched) and just inverts
    // the index at the call site.
    function yFor(s, H, nStrings) {
        return stringY(nStrings - 1 - s, H, nStrings);
    }

    // Size the backing store to the canvas's on-screen CSS pixels, respecting
    // device pixel ratio so the result is crisp on retina. Called on mount
    // and on window resize. The canvas itself takes its display size from
    // CSS (flex: 1), so we only touch width/height and the ctx transform.
    function sizeCanvasToBox() {
        if (!canvas || !ctx) return;
        const rect = canvas.getBoundingClientRect();
        const dpr = window.devicePixelRatio || 1;
        const pxW = Math.max(1, Math.floor(rect.width * dpr));
        const pxH = Math.max(1, Math.floor(rect.height * dpr));
        if (canvas.width !== pxW || canvas.height !== pxH) {
            canvas.width = pxW;
            canvas.height = pxH;
        }
        // Draw in CSS-pixel coordinates regardless of DPR
        ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    }

    function mountCanvas() {
        const player = document.getElementById('player');
        const hw = document.getElementById('highway');
        if (!player || !hw) return false;

        // Wrapper takes the highway's flex slot and centers the canvas
        // vertically + horizontally inside it. The canvas itself is a
        // shorter horizontal strip (Yousician style) instead of filling
        // the whole player area.
        wrap = document.createElement('div');
        wrap.id = 'jumpingtab-wrap';
        wrap.style.cssText = [
            'flex:1',
            'min-height:0',
            'display:flex',
            'align-items:center',
            'justify-content:center',
            'padding:0 24px',
        ].join(';');

        canvas = document.createElement('canvas');
        canvas.id = 'jumpingtab-canvas';
        canvas.style.cssText = [
            'width:100%',
            'max-width:1400px',
            'height:min(42vh, 360px)',
            'display:block',
            'background:#0f1420',
            'border-radius:10px',
            'box-shadow:0 8px 24px rgba(0,0,0,0.4)',
        ].join(';');

        wrap.appendChild(canvas);
        hw.insertAdjacentElement('afterend', wrap);
        ctx = canvas.getContext('2d');
        hw.style.display = 'none';
        audioEl = document.querySelector('audio');
        sizeCanvasToBox();
        window.addEventListener('resize', sizeCanvasToBox);
        return true;
    }

    function unmountCanvas() {
        if (raf) { cancelAnimationFrame(raf); raf = null; }
        window.removeEventListener('resize', sizeCanvasToBox);
        if (wrap) { wrap.remove(); wrap = null; canvas = null; ctx = null; }
        const hw = document.getElementById('highway');
        if (hw) hw.style.display = '';
        audioEl = null;
    }

    // ── Section color palette (cycled) ──────────────────────
    const SECTION_COLORS = [
        'rgba(110, 231, 255, 0.10)',  // cyan
        'rgba(183, 134, 255, 0.10)',  // purple
        'rgba(107, 255, 149, 0.10)',  // green
        'rgba(255, 194, 107, 0.10)',  // orange
        'rgba(255, 107, 139, 0.10)',  // pink
    ];

    function currentSection(sections, now) {
        if (!sections || !sections.length) return null;
        let cur = null;
        for (const sec of sections) {
            if (sec.time <= now) cur = sec;
            else break;
        }
        return cur;
    }

    // ── Renderer ─────────────────────────────────────────────
    function drawBackground(W, H, nStrings, colors, now) {
        // Base fill — rich navy with a soft radial vignette
        ctx.fillStyle = '#070b18';
        ctx.fillRect(0, 0, W, H);

        const topBand = TOP_PAD;
        const botBand = H - BOTTOM_PAD;
        const laneH = botBand - topBand;

        // Lane panel — slightly lighter, with rounded top/bottom so the
        // strings sit inside a visible "tab strip"
        const laneGrad = ctx.createLinearGradient(0, topBand, 0, botBand);
        laneGrad.addColorStop(0, '#0d1428');
        laneGrad.addColorStop(0.5, '#0a1024');
        laneGrad.addColorStop(1, '#0d1428');
        ctx.fillStyle = laneGrad;
        ctx.fillRect(0, topBand, W, laneH);

        // Section bands — subtle colored backgrounds keyed to their time range
        if (state.sections && state.sections.length) {
            const lo = now - BEHIND;
            const hi = now + AHEAD;
            for (let i = 0; i < state.sections.length; i++) {
                const sec = state.sections[i];
                const next = state.sections[i + 1];
                const t0 = sec.time;
                const t1 = next ? next.time : (state.songInfo.duration || t0 + 999);
                if (t1 < lo || t0 > hi) continue;
                const sx0 = timeX(t0, now, W);
                const sx1 = timeX(t1, now, W);
                ctx.fillStyle = SECTION_COLORS[i % SECTION_COLORS.length];
                ctx.fillRect(sx0, topBand, sx1 - sx0, laneH);
            }
        }

        // Beat / measure lines — thin verticals inside the lane
        if (state.beats && state.beats.length) {
            const lo = now - BEHIND;
            const hi = now + AHEAD;
            for (const b of state.beats) {
                if (b.time < lo || b.time > hi) continue;
                const bx = timeX(b.time, now, W);
                const isMeasure = b.measure != null && b.measure >= 0;
                ctx.strokeStyle = isMeasure ? 'rgba(200, 210, 240, 0.18)' : 'rgba(140, 150, 180, 0.08)';
                ctx.lineWidth = isMeasure ? 1.5 : 1;
                ctx.beginPath();
                ctx.moveTo(bx, topBand + 4);
                ctx.lineTo(bx, botBand - 4);
                ctx.stroke();
            }
        }

        // Hit zone — a vertical gradient strip centered on the hit line
        const hitX = W * HIT_LINE_FRAC;
        const zoneL = hitX - HIT_ZONE_WIDTH / 2;
        const zoneR = hitX + HIT_ZONE_WIDTH / 2;
        const zoneGrad = ctx.createLinearGradient(zoneL, 0, zoneR, 0);
        zoneGrad.addColorStop(0, 'rgba(110, 231, 255, 0)');
        zoneGrad.addColorStop(0.5, 'rgba(110, 231, 255, 0.18)');
        zoneGrad.addColorStop(1, 'rgba(110, 231, 255, 0)');
        ctx.fillStyle = zoneGrad;
        ctx.fillRect(zoneL, topBand, HIT_ZONE_WIDTH, laneH);

        // String lines — colored, drawn inside the lane
        ctx.lineWidth = 1.5;
        for (let s = 0; s < nStrings; s++) {
            const y = yFor(s, H, nStrings);
            ctx.strokeStyle = colors[s] + '60';
            ctx.beginPath();
            ctx.moveTo(0, y);
            ctx.lineTo(W, y);
            ctx.stroke();
        }

        // String labels on the left gutter
        ctx.font = 'bold 12px "SF Mono", Menlo, monospace';
        ctx.textBaseline = 'middle';
        ctx.textAlign = 'center';
        const labels = nStrings === 4 ? ['G','D','A','E'] : ['e','B','G','D','A','E'];
        for (let s = 0; s < nStrings; s++) {
            const y = yFor(s, H, nStrings);
            ctx.fillStyle = 'rgba(15, 20, 32, 0.88)';
            ctx.beginPath();
            ctx.arc(16, y, 10, 0, Math.PI * 2);
            ctx.fill();
            ctx.strokeStyle = colors[s] + '80';
            ctx.lineWidth = 1.5;
            ctx.stroke();
            ctx.fillStyle = colors[s];
            ctx.fillText(labels[s], 16, y + 0.5);
        }

        // Hit line — crisp bright line in the middle of the zone
        ctx.save();
        ctx.shadowColor = '#6ee7ff';
        ctx.shadowBlur = 24;
        ctx.strokeStyle = '#d6f6ff';
        ctx.lineWidth = 2.5;
        ctx.beginPath();
        ctx.moveTo(hitX, topBand);
        ctx.lineTo(hitX, botBand);
        ctx.stroke();
        ctx.restore();
    }

    // Edge fade — draw dark gradients at the left and right edges so notes
    // don't pop in/out. Called AFTER notes so it overlays everything in
    // the lane area.
    function drawEdgeFade(W, H) {
        const topBand = TOP_PAD;
        const botBand = H - BOTTOM_PAD;
        const laneH = botBand - topBand;
        const fadeW = W * EDGE_FADE_FRAC;

        const leftGrad = ctx.createLinearGradient(0, 0, fadeW, 0);
        leftGrad.addColorStop(0, 'rgba(7, 11, 24, 1)');
        leftGrad.addColorStop(1, 'rgba(7, 11, 24, 0)');
        ctx.fillStyle = leftGrad;
        ctx.fillRect(0, topBand, fadeW, laneH);

        const rightGrad = ctx.createLinearGradient(W - fadeW, 0, W, 0);
        rightGrad.addColorStop(0, 'rgba(7, 11, 24, 0)');
        rightGrad.addColorStop(1, 'rgba(7, 11, 24, 1)');
        ctx.fillStyle = rightGrad;
        ctx.fillRect(W - fadeW, topBand, fadeW, laneH);
    }

    // Header strip — song title / artist / arrangement / current section
    function drawHeader(W, H, now) {
        const info = state.songInfo || {};
        const sec = currentSection(state.sections, now);

        // Header background — dark strip across the top
        const hdrGrad = ctx.createLinearGradient(0, 0, 0, HEADER_H);
        hdrGrad.addColorStop(0, 'rgba(12, 16, 30, 0.95)');
        hdrGrad.addColorStop(1, 'rgba(12, 16, 30, 0.6)');
        ctx.fillStyle = hdrGrad;
        ctx.fillRect(0, 0, W, HEADER_H);

        // Left: title · artist
        ctx.font = '600 13px -apple-system, system-ui, sans-serif';
        ctx.textBaseline = 'middle';
        ctx.textAlign = 'left';
        ctx.fillStyle = '#e6ecff';
        const title = info.title || 'Unknown';
        ctx.fillText(title, 16, HEADER_H / 2);

        // Artist subtitle
        const titleW = ctx.measureText(title).width;
        ctx.font = '400 12px -apple-system, system-ui, sans-serif';
        ctx.fillStyle = 'rgba(200, 210, 230, 0.55)';
        if (info.artist) {
            ctx.fillText('· ' + info.artist, 16 + titleW + 8, HEADER_H / 2);
        }

        // Right: arrangement badge + current section
        ctx.textAlign = 'right';
        if (sec) {
            const label = sec.name || '';
            ctx.font = 'bold 11px "SF Mono", Menlo, monospace';
            const lw = ctx.measureText(label).width;
            const bx = W - 16 - lw - 12;
            ctx.fillStyle = 'rgba(110, 231, 255, 0.18)';
            if (ctx.roundRect) {
                ctx.beginPath();
                ctx.roundRect(bx, HEADER_H / 2 - 10, lw + 16, 20, 10);
                ctx.fill();
            } else {
                ctx.fillRect(bx, HEADER_H / 2 - 10, lw + 16, 20);
            }
            ctx.fillStyle = '#a6f0ff';
            ctx.fillText(label, W - 24, HEADER_H / 2 + 1);
        }

        if (info.arrangement) {
            ctx.font = '500 11px -apple-system, system-ui, sans-serif';
            ctx.fillStyle = 'rgba(200, 210, 230, 0.55)';
            const margin = sec ? (W - 16 - ctx.measureText((sec.name || '')).width - 32) : W - 16;
            ctx.fillText(info.arrangement, margin, HEADER_H / 2);
        }
    }

    // Progress bar along the bottom of the canvas
    function drawProgress(W, H, now) {
        const duration = (state.songInfo && state.songInfo.duration) || 0;
        if (duration <= 0) return;

        const barY = H - 22;
        const barH = 6;
        const barX = 16;
        const barW = W - 32;

        // Track
        ctx.fillStyle = 'rgba(200, 210, 230, 0.12)';
        if (ctx.roundRect) {
            ctx.beginPath();
            ctx.roundRect(barX, barY, barW, barH, barH / 2);
            ctx.fill();
        } else {
            ctx.fillRect(barX, barY, barW, barH);
        }

        // Fill
        const pct = Math.max(0, Math.min(1, now / duration));
        const fillW = barW * pct;
        const fillGrad = ctx.createLinearGradient(barX, 0, barX + barW, 0);
        fillGrad.addColorStop(0, '#6ee7ff');
        fillGrad.addColorStop(1, '#b786ff');
        ctx.fillStyle = fillGrad;
        if (ctx.roundRect) {
            ctx.beginPath();
            ctx.roundRect(barX, barY, fillW, barH, barH / 2);
            ctx.fill();
        } else {
            ctx.fillRect(barX, barY, fillW, barH);
        }

        // Time labels
        const fmt = (t) => {
            const m = Math.floor(t / 60);
            const s = Math.floor(t % 60);
            return m + ':' + (s < 10 ? '0' + s : s);
        };
        ctx.font = '500 10px "SF Mono", Menlo, monospace';
        ctx.fillStyle = 'rgba(200, 210, 230, 0.6)';
        ctx.textBaseline = 'middle';
        ctx.textAlign = 'left';
        ctx.fillText(fmt(now), barX, barY - 8);
        ctx.textAlign = 'right';
        ctx.fillText(fmt(duration), barX + barW, barY - 8);
    }

    // Distance-based radius: notes grow as they approach the hit line and
    // shrink as they leave. Max at hitX, base at edges.
    function noteRadius(x, hitX, W) {
        const dxRight = Math.abs(x - hitX);
        const span = Math.max(hitX, W - hitX);
        const t = 1 - Math.min(1, dxRight / (span * 0.6));
        return NOTE_BASE_R + (NOTE_MAX_R - NOTE_BASE_R) * Math.max(0, t);
    }

    function drawSustains(W, H, nStrings, colors, now) {
        if (!state.ready || !state.notes.length) return;
        const { start, end } = binaryVisibleRange(state.notes, now);
        const tailHeight = 8;
        for (let i = start; i < end; i++) {
            const n = state.notes[i];
            if (!n.sus || n.sus <= 0) continue;
            if (n.s < 0 || n.s >= nStrings) continue;
            const x0 = timeX(n.t, now, W);
            const x1 = timeX(n.t + n.sus, now, W);
            const y = yFor(n.s, H, nStrings);
            ctx.save();
            ctx.globalAlpha = 0.55;
            ctx.fillStyle = colors[n.s];
            // Rounded rect
            const r = tailHeight / 2;
            ctx.beginPath();
            ctx.moveTo(x0 + r, y - r);
            ctx.lineTo(x1 - r, y - r);
            ctx.arcTo(x1, y - r, x1, y, r);
            ctx.arcTo(x1, y + r, x1 - r, y + r, r);
            ctx.lineTo(x0 + r, y + r);
            ctx.arcTo(x0, y + r, x0, y, r);
            ctx.arcTo(x0, y - r, x0 + r, y - r, r);
            ctx.closePath();
            ctx.fill();
            ctx.restore();
        }
    }

    function arcControlPoint(x0, y0, x1, y1) {
        const midX = (x0 + x1) / 2;
        const dy = Math.abs(y1 - y0);
        const rise = Math.min(70, 20 + dy * 1.2);
        const midY = Math.min(y0, y1) - rise;
        return { cx: midX, cy: midY };
    }

    function drawArcs(W, H, nStrings, colors, now) {
        if (!state.ready || !state.arcs.length) return;
        const lo = now - BEHIND;
        const hi = now + AHEAD;

        ctx.save();
        ctx.strokeStyle = '#6ee7ff';
        ctx.globalAlpha = 0.7;
        ctx.lineWidth = 2;
        ctx.setLineDash([5, 4]);

        for (const arc of state.arcs) {
            if (arc.t1 < lo || arc.t0 > hi) continue;
            if (arc.s0 < 0 || arc.s0 >= nStrings) continue;
            if (arc.s1 < 0 || arc.s1 >= nStrings) continue;
            const x0 = timeX(arc.t0, now, W);
            const y0 = yFor(arc.s0, H, nStrings);
            const x1 = timeX(arc.t1, now, W);
            const y1 = yFor(arc.s1, H, nStrings);
            const { cx, cy } = arcControlPoint(x0, y0, x1, y1);
            ctx.beginPath();
            ctx.moveTo(x0, y0);
            ctx.quadraticCurveTo(cx, cy, x1, y1);
            ctx.stroke();
        }

        ctx.restore();
    }

    // Technique pairs — for HO/PO/slide pairs on the same string, render
    // both notes as a single fused capsule (stadium shape) instead of two
    // separate circles. Visually communicates "these belong together" and
    // leaves room for the technique arc + letter above.
    function drawTechniquePairs(W, H, nStrings, colors, now) {
        if (!state.ready || !state.techArcs || !state.techArcs.length) return;
        const lo = now - BEHIND;
        const hi = now + AHEAD;

        const R = 14;
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';
        ctx.font = 'bold 13px "SF Mono", Menlo, monospace';

        for (const a of state.techArcs) {
            if (a.t1 < lo || a.t0 > hi) continue;
            if (a.s < 0 || a.s >= nStrings) continue;

            const x0 = timeX(a.t0, now, W);
            const x1 = timeX(a.t1, now, W);
            const y = yFor(a.s, H, nStrings);
            const color = colors[a.s];

            // Use the later note's time for fade so the capsule fades as
            // a unit when it's behind the hit line.
            let alpha = 1;
            const dt = now - a.t1;
            if (dt > 0) {
                alpha = 1 - (dt / FADE_SECONDS);
                if (alpha <= 0) continue;
            }

            ctx.save();
            ctx.globalAlpha = alpha;

            // Capsule body — stadium shape from (x0-R) to (x1+R), height 2R
            const left = x0 - R;
            const top = y - R;
            const width = (x1 - x0) + 2 * R;
            const height = 2 * R;

            ctx.shadowColor = color;
            ctx.shadowBlur = 10;
            ctx.fillStyle = color;
            ctx.beginPath();
            if (ctx.roundRect) {
                ctx.roundRect(left, top, width, height, R);
            } else {
                // Fallback for very old browsers
                ctx.moveTo(left + R, top);
                ctx.lineTo(left + width - R, top);
                ctx.arc(left + width - R, y, R, -Math.PI / 2, Math.PI / 2);
                ctx.lineTo(left + R, top + height);
                ctx.arc(left + R, y, R, Math.PI / 2, (3 * Math.PI) / 2);
                ctx.closePath();
            }
            ctx.fill();

            // White outline
            ctx.shadowBlur = 0;
            ctx.lineWidth = 2;
            ctx.strokeStyle = 'rgba(255, 255, 255, 0.85)';
            ctx.stroke();

            // Fret numbers at each end
            ctx.fillStyle = '#0a0f1c';
            ctx.fillText(String(a.f0), x0, y + 1);
            ctx.fillText(String(a.f1), x1, y + 1);

            ctx.restore();
        }
    }

    // Technique arcs — curves above the notes on the same string for
    // hammer-on (h), pull-off (p), or slide (s). These sit above the note
    // row as a solid curve with a small letter label, mirroring standard
    // tab notation.
    function drawTechniqueArcs(W, H, nStrings, colors, now) {
        if (!state.ready || !state.techArcs || !state.techArcs.length) return;
        const lo = now - BEHIND;
        const hi = now + AHEAD;

        ctx.save();
        ctx.lineWidth = 1.8;
        ctx.lineCap = 'round';
        ctx.font = 'bold 10px monospace';
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';

        for (const a of state.techArcs) {
            if (a.t1 < lo || a.t0 > hi) continue;
            if (a.s < 0 || a.s >= nStrings) continue;
            const x0 = timeX(a.t0, now, W);
            const x1 = timeX(a.t1, now, W);
            if (x1 - x0 < 6) continue;  // too close to be legible
            const y = yFor(a.s, H, nStrings);
            // Curve sits ~18px above the note row
            const lift = 20;
            const cx = (x0 + x1) / 2;
            const cy = y - lift;

            // Color codes: hammer-on cyan-ish, pull-off warm, slide white
            const color = a.type === 'h' ? '#ffc86b'
                        : a.type === 'p' ? '#ff8ab6'
                        : '#ffffff';
            ctx.strokeStyle = color;
            ctx.globalAlpha = 0.85;
            ctx.beginPath();
            ctx.moveTo(x0, y - 4);
            ctx.quadraticCurveTo(cx, cy, x1, y - 4);
            ctx.stroke();

            // Letter label centered above the curve
            ctx.globalAlpha = 1;
            ctx.fillStyle = color;
            ctx.fillText(a.type, cx, cy + 1);
        }

        ctx.restore();
    }

    function findActiveArc(arcs, now) {
        // Linear scan is fine — arcs.length is in the hundreds, this is 60fps-safe.
        // Return the arc whose [t0, t1] contains now, or the most-recent past arc
        // if we're between arcs (rest).
        let best = null;
        for (const a of arcs) {
            if (a.t0 <= now && now <= a.t1) return a;
            if (a.t1 < now && (!best || a.t1 > best.t1)) best = a;
        }
        return best;
    }

    function nearestNoteAtHit(notes, now, hitX, W) {
        // Find the note whose current x is closest to the hit line.
        const { start, end } = binaryVisibleRange(notes, now);
        let best = null, bestDx = Infinity;
        for (let i = start; i < end; i++) {
            const n = notes[i];
            const x = timeX(n.t, now, W);
            const dx = Math.abs(x - hitX);
            if (dx < bestDx) { bestDx = dx; best = { note: n, dx, x }; }
        }
        return best;
    }

    function drawBall(W, H, nStrings, colors, now) {
        if (!state.ready || !state.arcs.length) return;
        const arc = findActiveArc(state.arcs, now);
        if (!arc) return;

        const x0 = timeX(arc.t0, now, W);
        const y0 = yFor(arc.s0, H, nStrings);
        const x1 = timeX(arc.t1, now, W);
        const y1 = yFor(arc.s1, H, nStrings);
        const { cx, cy } = arcControlPoint(x0, y0, x1, y1);

        const u = Math.max(0, Math.min(1, (now - arc.t0) / Math.max(0.0001, arc.t1 - arc.t0)));
        const p = bezierPoint(x0, y0, cx, cy, x1, y1, u);

        // Squash when we're inside SQUASH_WINDOW_MS of any note crossing the hit line
        const hitX = W * HIT_LINE_FRAC;
        const nearest = nearestNoteAtHit(state.notes, now, hitX, W);
        let sx = 1, sy = 1;
        if (nearest && nearest.dx < 14) {
            const msFromNote = Math.abs(now - nearest.note.t) * 1000;
            if (msFromNote < SQUASH_WINDOW_MS) {
                const k = 1 - (msFromNote / SQUASH_WINDOW_MS);  // 1 at t=note, 0 at edge
                sx = 1 + 0.25 * k;
                sy = 1 - 0.40 * k;
            }
        }

        ctx.save();
        ctx.shadowColor = '#6ee7ff';
        ctx.shadowBlur = 18;
        ctx.translate(p.x, p.y);
        ctx.scale(sx, sy);
        // Layered ball: outer glow ring + inner bright core
        ctx.fillStyle = 'rgba(166, 240, 255, 0.6)';
        ctx.beginPath();
        ctx.arc(0, 0, 11, 0, Math.PI * 2);
        ctx.fill();
        ctx.shadowBlur = 0;
        ctx.fillStyle = '#ffffff';
        ctx.beginPath();
        ctx.arc(0, 0, 6, 0, Math.PI * 2);
        ctx.fill();
        ctx.restore();
    }

    // Bend indicators — a bright vertical arrow above any note with bn > 0,
    // labeled with the bend amount in standard tab notation. Rendered on
    // top of notes (both normal fret circles and fused capsules) so it's
    // visible regardless of which note presentation is used.
    function drawBends(W, H, nStrings, colors, now) {
        if (!state.ready || !state.notes.length) return;
        const { start, end } = binaryVisibleRange(state.notes, now);

        ctx.textAlign = 'left';
        ctx.textBaseline = 'middle';
        ctx.font = 'bold 11px "SF Mono", Menlo, monospace';

        for (let i = start; i < end; i++) {
            const n = state.notes[i];
            if (!n.bn || n.bn <= 0) continue;
            if (n.s < 0 || n.s >= nStrings) continue;

            const x = timeX(n.t, now, W);
            const y = yFor(n.s, H, nStrings);

            // Fade with the note
            let alpha = 1;
            const dt = now - n.t;
            if (dt > 0) {
                alpha = 1 - (dt / FADE_SECONDS);
                if (alpha <= 0) continue;
            }

            // Arrow geometry: starts at the top of the fret circle and
            // points up; length scales slightly with bend amount (bigger
            // bend = longer arrow) so half-bends and full bends look
            // different at a glance.
            const noteR = 14;
            const baseY = y - noteR - 2;
            const len = 14 + Math.min(12, n.bn * 6);
            const tipY = baseY - len;
            const headH = 5;
            const headW = 4;

            ctx.save();
            ctx.globalAlpha = alpha;
            ctx.shadowColor = '#ffd35a';
            ctx.shadowBlur = 8;
            ctx.strokeStyle = '#ffd35a';
            ctx.fillStyle = '#ffd35a';
            ctx.lineWidth = 2;
            ctx.lineCap = 'round';

            // Shaft
            ctx.beginPath();
            ctx.moveTo(x, baseY);
            ctx.lineTo(x, tipY + headH);
            ctx.stroke();

            // Arrowhead (filled triangle)
            ctx.shadowBlur = 0;
            ctx.beginPath();
            ctx.moveTo(x, tipY);
            ctx.lineTo(x - headW, tipY + headH);
            ctx.lineTo(x + headW, tipY + headH);
            ctx.closePath();
            ctx.fill();

            // Label to the right of the tip
            ctx.fillStyle = '#ffd35a';
            ctx.shadowColor = '#000000';
            ctx.shadowBlur = 3;
            ctx.fillText(bendText(n.bn), x + headW + 3, tipY + 4);

            ctx.restore();
        }
    }

    function drawNotes(W, H, nStrings, colors, now) {
        if (!state.ready || !state.notes.length) return;
        const { start, end } = binaryVisibleRange(state.notes, now);
        const hitX = W * HIT_LINE_FRAC;

        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';

        for (let i = start; i < end; i++) {
            const n = state.notes[i];
            if (n.s < 0 || n.s >= nStrings) continue;
            if (state.techPaired && state.techPaired.has(n)) continue;

            const x = timeX(n.t, now, W);
            const y = yFor(n.s, H, nStrings);
            const color = colors[n.s];
            const R = noteRadius(x, hitX, W);

            let alpha = 1;
            const dt = now - n.t;
            if (dt > 0) {
                alpha = 1 - (dt / FADE_SECONDS);
                if (alpha <= 0) continue;
            }

            ctx.save();
            ctx.globalAlpha = alpha;

            // Colored glow halo
            ctx.shadowColor = color;
            ctx.shadowBlur = 14;
            ctx.fillStyle = color;
            ctx.beginPath();
            ctx.arc(x, y, R, 0, Math.PI * 2);
            ctx.fill();

            // Inner gradient for a subtle 3D feel
            ctx.shadowBlur = 0;
            const innerGrad = ctx.createRadialGradient(
                x - R * 0.3, y - R * 0.4, R * 0.1,
                x, y, R
            );
            innerGrad.addColorStop(0, 'rgba(255, 255, 255, 0.45)');
            innerGrad.addColorStop(0.5, 'rgba(255, 255, 255, 0)');
            innerGrad.addColorStop(1, 'rgba(0, 0, 0, 0.25)');
            ctx.fillStyle = innerGrad;
            ctx.beginPath();
            ctx.arc(x, y, R, 0, Math.PI * 2);
            ctx.fill();

            // Crisp outline
            ctx.lineWidth = 2;
            ctx.strokeStyle = 'rgba(255, 255, 255, 0.9)';
            ctx.beginPath();
            ctx.arc(x, y, R, 0, Math.PI * 2);
            ctx.stroke();

            // Fret number
            ctx.font = 'bold ' + Math.round(R * 0.95) + 'px "SF Mono", Menlo, monospace';
            ctx.fillStyle = '#0a0f1c';
            ctx.fillText(String(n.f), x, y + 1);
            ctx.restore();
        }
    }

    function drawFrame(now) {
        if (!ctx || !canvas) return;
        const W = canvas.clientWidth;
        const H = canvas.clientHeight;
        if (W === 0 || H === 0) return;
        const nStrings = (state.tuning && state.tuning.length === 4) ? 4 : 6;
        const colors = colorsFor(nStrings);

        drawBackground(W, H, nStrings, colors, now);
        drawSustains(W, H, nStrings, colors, now);
        drawArcs(W, H, nStrings, colors, now);
        drawTechniquePairs(W, H, nStrings, colors, now);
        drawTechniqueArcs(W, H, nStrings, colors, now);
        drawNotes(W, H, nStrings, colors, now);
        drawBends(W, H, nStrings, colors, now);
        drawBall(W, H, nStrings, colors, now);
        drawEdgeFade(W, H);
        drawHeader(W, H, now);
        drawProgress(W, H, now);
    }

    function tick() {
        if (!active) return;
        const now = audioEl ? audioEl.currentTime : 0;
        drawFrame(now);
        raf = requestAnimationFrame(tick);
    }

    // ── Toggle + button ──────────────────────────────────────
    function toggle() {
        if (!active) {
            if (!state.ready) {
                console.warn('[jumpingtab] not ready — song data still loading');
                return;
            }
            if (!mountCanvas()) return;
            active = true;
            if (raf) cancelAnimationFrame(raf);
            tick();
            const b = document.getElementById('btn-jt');
            if (b) b.className = 'px-3 py-1.5 bg-cyan-900/50 rounded-lg text-xs text-cyan-300 transition';
        } else {
            active = false;
            if (raf) { cancelAnimationFrame(raf); raf = null; }
            unmountCanvas();
            const b = document.getElementById('btn-jt');
            if (b) b.className = 'px-3 py-1.5 bg-dark-600 hover:bg-dark-500 rounded-lg text-xs text-gray-400 transition';
        }
    }

    function injectBtn() {
        const c = document.getElementById('player-controls');
        if (!c || document.getElementById('btn-jt')) return;
        const last = c.querySelector('button:last-child');
        const b = document.createElement('button');
        b.id = 'btn-jt';
        b.className = 'px-3 py-1.5 bg-dark-600 hover:bg-dark-500 rounded-lg text-xs text-gray-400 transition';
        b.textContent = 'Jumping Tab';
        b.title = 'Toggle Yousician-style jumping tab view';
        b.disabled = true;
        b.style.opacity = '0.5';
        b.onclick = toggle;
        c.insertBefore(b, last);
    }

    // Expose for manual poking / future tests
    window.__jumpingtab_state = state;
    window.__jumpingtab_connect = connect;

    // ── Hook installation ────────────────────────────────────
    const _origPlay = window.playSong;
    window.playSong = async function (filename, arrangement) {
        // Tear down any currently-active view before switching songs
        if (active) {
            active = false;
            if (raf) { cancelAnimationFrame(raf); raf = null; }
            unmountCanvas();
            const b = document.getElementById('btn-jt');
            if (b) b.className = 'px-3 py-1.5 bg-dark-600 hover:bg-dark-500 rounded-lg text-xs text-gray-400 transition';
        }

        await _origPlay(filename, arrangement);
        injectBtn();
        const btn = document.getElementById('btn-jt');
        if (btn) { btn.disabled = true; btn.style.opacity = '0.5'; btn.title = 'Loading…'; }

        try {
            await connect(filename, arrangement);
            console.log('[jumpingtab] loaded',
                state.notes.length, 'notes,', state.arcs.length, 'arcs');
            if (btn) { btn.disabled = false; btn.style.opacity = ''; btn.title = 'Toggle Yousician-style jumping tab view'; }
        } catch (e) {
            console.warn('[jumpingtab] connect failed:', e.message);
            if (btn) { btn.disabled = true; btn.style.opacity = '0.5'; btn.title = 'Jumping Tab unavailable: ' + e.message; }
        }
    };

    const _origShow = window.showScreen;
    window.showScreen = function (id) {
        if (id !== 'player') {
            if (active) {
                active = false;
                unmountCanvas();
            }
            if (state.ws) { try { state.ws.close(); } catch (e) {} state.ws = null; }
        }
        if (typeof _origShow === 'function') _origShow(id);
    };

    // Wrap changeArrangement so switching Lead / Rhythm / Bass in the
    // player dropdown re-runs our connect() with the new arrangement
    // index. The ws builds a fresh note/arc/beat set for the new
    // arrangement; if the tab view is currently active, we redraw from
    // whatever the new state is.
    const _origChangeArr = window.changeArrangement;
    window.changeArrangement = function (index) {
        if (typeof _origChangeArr === 'function') _origChangeArr(index);
        if (!state.filename) return;
        const btn = document.getElementById('btn-jt');
        if (btn) { btn.disabled = true; btn.style.opacity = '0.5'; btn.title = 'Loading…'; }
        connect(state.filename, parseInt(index, 10))
            .then(() => {
                if (btn) { btn.disabled = false; btn.style.opacity = ''; btn.title = 'Toggle Yousician-style jumping tab view'; }
            })
            .catch((e) => {
                console.warn('[jumpingtab] arrangement switch failed:', e.message);
                if (btn) { btn.disabled = true; btn.style.opacity = '0.5'; btn.title = 'Jumping Tab unavailable: ' + e.message; }
            });
    };

    console.log('[jumpingtab] plugin loaded');
})();
