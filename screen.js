(function () {
    'use strict';

    // ── Constants ─────────────────────────────────────────────
    const AHEAD = 5.5;
    const BEHIND = 1.2;
    const HIT_LINE_FRAC = 0.18;
    const FADE_SECONDS = 1.0;
    const SQUASH_WINDOW_MS = 60;
    const IMPACT_DURATION = 0.45;   // seconds — ring expansion after a note crosses the hit line
    const DISABLE_RINGS = true;   // set to true to disable expanding rings on note hits
    const TOP_PAD = 60;           // room for header strip
    const BOTTOM_PAD = 36;        // room for progress bar
    const HIT_ZONE_WIDTH = 56;    // wide glowing strip around hit line
    const EDGE_FADE_FRAC = 0.06;  // % of canvas width to fade at edges
    const NOTE_BASE_R = 18;
    const NOTE_MAX_R = 18;        // consistent radius for all notes
    const HEADER_H = 36;

    const GUITAR_COLORS = ['#ff6b8b', '#ffe66b', '#6bd5ff', '#ffa56b', '#6bff95', '#c56bff'];
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
                    arcs.push({
                        t0: prev.t, t1: n.t, s: n.s, type,
                        f0: prev.f, f1: n.f,
                        n0: prev, n1: n,
                    });
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
            state.chords = [];
            state.chordTemplates = [];
            state.songInfo = {};
            state.ready = false;

            const proto = location.protocol === 'https:' ? 'wss:' : 'ws:';
            const qs = (arrangementIdx != null && arrangementIdx >= 0)
                ? `?arrangement=${arrangementIdx}` : '';
            const url = `${proto}//${location.host}/ws/highway/${decodeURIComponent(filename)}${qs}`;
            const ws = new WebSocket(url);
            state.ws = ws;

            let singleNotesCount = 0;
            let chordNotesCount = 0;

            const finalize = () => {
                if (state.ready) return;
                state.notes.sort((a, b) => a.t - b.t);
                state.chords.sort((a, b) => a.t - b.t);

                // Precompute per-note neighbor gaps (in seconds) for
                // same-string neighbors, so drawNotes can clamp the
                // radius and avoid visual overlap in dense passages.
                // Chord teammates share a timestamp — skip those via
                // an epsilon check.
                const lastIdxByString = new Map();
                const EPS_T = 1e-4;
                for (let i = 0; i < state.notes.length; i++) {
                    const n = state.notes[i];
                    n._gapL = Infinity;
                    n._gapR = Infinity;
                    const prevIdx = lastIdxByString.get(n.s);
                    if (prevIdx != null) {
                        const prev = state.notes[prevIdx];
                        const gap = n.t - prev.t;
                        if (gap > EPS_T) {
                            n._gapL = gap;
                            if (gap < prev._gapR) prev._gapR = gap;
                        }
                    }
                    lastIdxByString.set(n.s, i);
                }

                state.arcs = buildTrajectories(state.notes);
                const tech = buildTechniqueArcs(state.notes);
                state.techArcs = tech.arcs;
                state.techPaired = tech.paired;
                state.ready = true;
                console.log('[jumpingtab] ready —',
                    singleNotesCount, 'single notes +',
                    chordNotesCount, 'chord notes =',
                    state.notes.length, 'total,',
                    state.chords.length, 'chords,',
                    state.chordTemplates.length, 'templates,',
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
                } else if (msg.type === 'chord_templates') {
                    // Store chord templates as an array so IDs match chord events.
                    state.chordTemplates = msg.data || [];
                    console.log('[jumpingtab] received', state.chordTemplates.length, 'chord templates');
                } else if (msg.type === 'chords') {
                    // Store chord events (time-based) AND expand into individual notes.
                    // Chord events: {t, id, hd, notes}
                    state.chords = state.chords.concat(msg.data || []);
                    for (const c of msg.data || []) {
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
                    console.log('[jumpingtab] received', (msg.data || []).length, 'chords');
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
    let wrap = null;
    let noteCanvas = null;
    let chordCanvas = null;
    let noteCtx = null;
    let chordCtx = null;
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
        if (!noteCanvas || !noteCtx || !chordCanvas || !chordCtx) return;
        const noteRect = noteCanvas.getBoundingClientRect();
        const chordRect = chordCanvas.getBoundingClientRect();
        const dpr = window.devicePixelRatio || 1;

        const notePxW = Math.max(1, Math.floor(noteRect.width * dpr));
        const notePxH = Math.max(1, Math.floor(noteRect.height * dpr));
        if (noteCanvas.width !== notePxW || noteCanvas.height !== notePxH) {
            noteCanvas.width = notePxW;
            noteCanvas.height = notePxH;
        }
        noteCtx.setTransform(dpr, 0, 0, dpr, 0, 0);

        const chordPxW = Math.max(1, Math.floor(chordRect.width * dpr));
        const chordPxH = Math.max(1, Math.floor(chordRect.height * dpr));
        if (chordCanvas.width !== chordPxW || chordCanvas.height !== chordPxH) {
            chordCanvas.width = chordPxW;
            chordCanvas.height = chordPxH;
        }
        chordCtx.setTransform(dpr, 0, 0, dpr, 0, 0);
    }

    function mountCanvas() {
        const player = document.getElementById('player');
        const hw = document.getElementById('highway');
        if (!player || !hw) return false;

        // Wrapper takes the highway's flex slot and stacks the chord and note canvases.
        wrap = document.createElement('div');
        wrap.id = 'jumpingtab-wrap';
        wrap.style.cssText = [
            'flex:1',
            'min-height:0',
            'display:flex',
            'flex-direction:column',
            'align-items:center',
            'justify-content:center',
            'padding:0 24px',
            'gap:12px',
            'width:95%',
            'height:95%',
            'margin:0 auto',
        ].join(';');

        chordCanvas = document.createElement('canvas');
        chordCanvas.id = 'jumpingtab-chord-canvas';
        chordCanvas.style.cssText = [
            'width:100%',
            'max-width:1400px',
            'flex:0.35',
            'min-height:0',
            'display:block',
            'background:#090f18',
            'border-radius:10px',
            'box-shadow:0 8px 24px rgba(0,0,0,0.3)',
        ].join(';');

        noteCanvas = document.createElement('canvas');
        noteCanvas.id = 'jumpingtab-canvas';
        noteCanvas.style.cssText = [
            'width:100%',
            'max-width:1400px',
            'flex:0.65',
            'min-height:0',
            'display:block',
            'background:#0f1420',
            'border-radius:10px',
            'box-shadow:0 8px 24px rgba(0,0,0,0.4)',
        ].join(';');

        wrap.appendChild(chordCanvas);
        wrap.appendChild(noteCanvas);
        hw.insertAdjacentElement('afterend', wrap);

        chordCtx = chordCanvas.getContext('2d');
        noteCtx = noteCanvas.getContext('2d');
        ctx = noteCtx;
        hw.style.display = 'none';
        audioEl = document.querySelector('audio');
        sizeCanvasToBox();
        window.addEventListener('resize', sizeCanvasToBox);
        return true;
    }

    function unmountCanvas() {
        if (raf) { cancelAnimationFrame(raf); raf = null; }
        window.removeEventListener('resize', sizeCanvasToBox);
        if (wrap) { wrap.remove(); wrap = null; noteCanvas = null; chordCanvas = null; noteCtx = null; chordCtx = null; ctx = null; }
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
    function drawStringLabels(W, H, nStrings, colors) {
        ctx.font = 'bold 12px "SF Mono", Menlo, monospace';
        ctx.textBaseline = 'middle';
        ctx.textAlign = 'center';
        const labels = nStrings === 4 ? ['E','A','D','G'] : ['E','A','D','G','B','e'];
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
    }

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

    // Convert a gap in seconds to a gap in canvas pixels at the current
    // time-to-x mapping. The lane spans AHEAD seconds from hitX to the
    // right edge, so 1 second = (W - hitX) / AHEAD pixels.
    function secondsToPx(seconds, W) {
        const hitX = W * HIT_LINE_FRAC;
        return seconds * (W - hitX) / AHEAD;
    }

    // Clamp a note radius to whatever fits between its same-string
    // neighbors at the current scale, with a floor so very dense runs
    // still render a visible dot rather than shrinking to nothing.
    const MIN_NOTE_R = 6;
    function clampByNeighbors(baseR, n, W) {
        const gap = Math.min(n._gapL || Infinity, n._gapR || Infinity);
        if (!isFinite(gap)) return baseR;
        const gapPx = secondsToPx(gap, W);
        // Leave a 3px visual gutter between adjacent notes
        const maxR = Math.max(MIN_NOTE_R, gapPx / 2 - 3);
        return Math.min(baseR, maxR);
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

        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';

        for (const a of state.techArcs) {
            if (a.t1 < lo || a.t0 > hi) continue;
            if (a.s < 0 || a.s >= nStrings) continue;

            const x0 = timeX(a.t0, now, W);
            const x1 = timeX(a.t1, now, W);
            const y = yFor(a.s, H, nStrings);
            const color = colors[a.s];

            // Radius clamped by outer neighbors — capsule shouldn't overlap
            // the note before (via n0._gapL) or after (via n1._gapR).
            const leftClamp = a.n0 ? clampByNeighbors(NOTE_BASE_R, a.n0, W) : NOTE_BASE_R;
            const rightClamp = a.n1 ? clampByNeighbors(NOTE_BASE_R, a.n1, W) : NOTE_BASE_R;
            const R = Math.min(leftClamp, rightClamp);
            ctx.font = 'bold ' + Math.round(R * 0.95) + 'px "SF Mono", Menlo, monospace';

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

    // Impact rings — when a note crosses the hit line, fire a ring that
    // stays anchored at (hitX, string y) and expands outward while fading,
    // colored to match the string. Gives the "I hit that one" feedback.
    // Also draws a brief full-string flash line so the impact feels like
    // it energises the string.
    function drawImpacts(W, H, nStrings, colors, now) {
        if (!state.ready || !state.notes.length) return;
        const { start, end } = binaryVisibleRange(state.notes, now);
        const hitX = W * HIT_LINE_FRAC;

        for (let i = start; i < end; i++) {
            const n = state.notes[i];
            if (n.s < 0 || n.s >= nStrings) continue;
            const dt = now - n.t;
            if (dt < 0 || dt >= IMPACT_DURATION) continue;

            // Ease-out curve: starts fast, slows down. Good for impacts.
            const p = dt / IMPACT_DURATION;
            const ease = 1 - Math.pow(1 - p, 2);
            const y = yFor(n.s, H, nStrings);
            const color = colors[n.s];

            // Expanding ring: grows from noteR out to ~3.2x, alpha fades
            const baseR = 14;
            const expansion = DISABLE_RINGS ? 0 : ease * 2.2;
            const r = baseR * (1 + expansion);
            const alpha = (1 - p) * 0.85;

            ctx.save();
            ctx.globalAlpha = alpha;
            ctx.strokeStyle = color;
            ctx.lineWidth = 3 - (DISABLE_RINGS ? 0 : ease * 2);  // thick → thin
            ctx.shadowColor = color;
            ctx.shadowBlur = 18;
            ctx.beginPath();
            ctx.arc(hitX, y, r, 0, Math.PI * 2);
            ctx.stroke();

            // Secondary inner ring in white for extra pop on fresh hits
            if (p < 0.5) {
                const expansion2 = DISABLE_RINGS ? 0 : ease * 1.2;
                ctx.globalAlpha = (1 - p * 2) * 0.6;
                ctx.strokeStyle = '#ffffff';
                ctx.shadowBlur = 10;
                ctx.lineWidth = 2;
                ctx.beginPath();
                ctx.arc(hitX, y, baseR * (1 + expansion2), 0, Math.PI * 2);
                ctx.stroke();
            }

            // Horizontal string flash — a bright streak along the string
            // for ~120ms, like plucking the string.
            if (p < 0.3) {
                const flashAlpha = (1 - p / 0.3) * 0.7;
                ctx.shadowBlur = 0;
                ctx.globalAlpha = flashAlpha;
                const flashGrad = ctx.createLinearGradient(hitX - 80, 0, hitX + 80, 0);
                flashGrad.addColorStop(0, 'rgba(255, 255, 255, 0)');
                flashGrad.addColorStop(0.5, color);
                flashGrad.addColorStop(1, 'rgba(255, 255, 255, 0)');
                ctx.strokeStyle = flashGrad;
                ctx.lineWidth = 3;
                ctx.beginPath();
                ctx.moveTo(hitX - 80, y);
                ctx.lineTo(hitX + 80, y);
                ctx.stroke();
            }

            ctx.restore();
        }
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
            const R = clampByNeighbors(NOTE_MAX_R, n, W);

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

    // ── Chord display ───────────────────────────────────────
    function findActiveChord(chords, now) {
        // Find the chord whose time is closest to now (most recently started)
        let best = null;
        for (const c of chords) {
            if (c.t <= now && (!best || c.t > best.t)) {
                best = c;
            }
        }
        return best;
    }

    function roundRect(ctx, x, y, width, height, radius) {
        if (typeof radius === 'undefined') radius = 5;
        if (typeof radius === 'number') radius = {tl: radius, tr: radius, br: radius, bl: radius};
        const {tl, tr, br, bl} = radius;
        ctx.beginPath();
        ctx.moveTo(x + tl, y);
        ctx.lineTo(x + width - tr, y);
        ctx.quadraticCurveTo(x + width, y, x + width, y + tr);
        ctx.lineTo(x + width, y + height - br);
        ctx.quadraticCurveTo(x + width, y + height, x + width - br, y + height);
        ctx.lineTo(x + bl, y + height);
        ctx.quadraticCurveTo(x, y + height, x, y + height - bl);
        ctx.lineTo(x, y + tl);
        ctx.quadraticCurveTo(x, y, x + tl, y);
        ctx.closePath();
    }

    function drawChordDiagram(x, y, chordName, frets, nStrings) {
        // Draw a miniature chord diagram (6 or 4 strings)
        const diagW = 50;
        const diagH = 60;
        const stringSpacing = diagW / Math.max(3, nStrings - 1);
        const fretH = 12;

        // Background
        ctx.fillStyle = 'rgba(20, 30, 50, 0.95)';
        ctx.fillRect(x - diagW / 2, y, diagW, diagH + 20);

        // Border
        ctx.strokeStyle = 'rgba(110, 231, 255, 0.5)';
        ctx.lineWidth = 1;
        ctx.strokeRect(x - diagW / 2, y, diagW, diagH + 20);

        // Chord name label
        ctx.font = 'bold 11px "SF Mono"';
        ctx.fillStyle = '#6ee7ff';
        ctx.textAlign = 'center';
        ctx.textBaseline = 'top';
        ctx.fillText(chordName, x, y + 2);

        // Diagram top (nut or fret 1 indicator)
        const diagTop = y + 18;

        // Vertical string lines
        ctx.strokeStyle = 'rgba(150, 160, 180, 0.6)';
        ctx.lineWidth = 1;
        for (let s = 0; s < nStrings; s++) {
            const sx = x - diagW / 2 + 5 + (s * stringSpacing);
            ctx.beginPath();
            ctx.moveTo(sx, diagTop);
            ctx.lineTo(sx, diagTop + 48);
            ctx.stroke();
        }

        // Horizontal fret lines
        ctx.strokeStyle = 'rgba(100, 110, 130, 0.4)';
        ctx.lineWidth = 1;
        for (let f = 0; f < 5; f++) {
            const fy = diagTop + f * fretH;
            ctx.beginPath();
            ctx.moveTo(x - diagW / 2 + 5, fy);
            ctx.lineTo(x - diagW / 2 + 5 + diagW - 10, fy);
            ctx.stroke();
        }

        // Finger positions (dots on diagram)
        if (frets && frets.length) {
            ctx.fillStyle = 'rgba(107, 255, 149, 0.8)';
            for (let s = 0; s < Math.min(nStrings, frets.length); s++) {
                const fret = frets[s];
                if (fret && fret > 0) {
                    const sx = x - diagW / 2 + 5 + (s * stringSpacing);
                    const fy = diagTop + fret * fretH - fretH / 2;
                    ctx.beginPath();
                    ctx.arc(sx, fy, 4, 0, Math.PI * 2);
                    ctx.fill();
                    // Fret number inside dot
                    ctx.font = 'bold 7px monospace';
                    ctx.fillStyle = '#0a0f1c';
                    ctx.textAlign = 'center';
                    ctx.textBaseline = 'middle';
                    ctx.fillText(String(fret), sx, fy);
                }
            }
            // X marks for muted strings
            ctx.strokeStyle = 'rgba(255, 107, 139, 0.7)';
            ctx.lineWidth = 1.5;
            for (let s = 0; s < Math.min(nStrings, frets.length); s++) {
                const fret = frets[s];
                if (fret === 0 || fret === '0' || fret === null) {
                    // Muted or open string might show as 0 or null
                }
            }
        }
    }

    function drawChordDiagramBox(x, y, width, height, frets, fingers, nStrings) {
        const stringCount = Math.min(nStrings, Math.max(4, frets.length));
        const diagWidth = 140;
        const diagHeight = 170;
        const diagX = x + (width - diagWidth) / 2;
        const diagY = y + 80;

        const stringSpacing = diagWidth / Math.max(1, stringCount - 1);
        const fretSpacing = diagHeight / 5;
        const nutY = diagY;

        chordCtx.strokeStyle = 'rgba(200, 220, 255, 0.6)';
        chordCtx.lineWidth = 2.5;
        for (let i = 0; i < stringCount; i++) {
            const sx = diagX + i * stringSpacing;
            chordCtx.beginPath();
            chordCtx.moveTo(sx, nutY);
            chordCtx.lineTo(sx, nutY + diagHeight);
            chordCtx.stroke();
        }

        chordCtx.strokeStyle = 'rgba(180, 200, 240, 0.35)';
        chordCtx.lineWidth = 1.5;
        for (let f = 0; f <= 5; f++) {
            const fy = nutY + f * fretSpacing;
            chordCtx.beginPath();
            chordCtx.moveTo(diagX, fy);
            chordCtx.lineTo(diagX + diagWidth, fy);
            chordCtx.stroke();
        }

        chordCtx.strokeStyle = 'rgba(255, 255, 255, 0.88)';
        chordCtx.lineWidth = 4;
        chordCtx.beginPath();
        chordCtx.moveTo(diagX, nutY);
        chordCtx.lineTo(diagX + diagWidth, nutY);
        chordCtx.stroke();

        chordCtx.textAlign = 'center';
        chordCtx.textBaseline = 'middle';

        for (let i = 0; i < stringCount; i++) {
            const sx = diagX + i * stringSpacing;
            const fret = frets[i];
            const finger = fingers[i];
            const topY = nutY - 6;

            if (fret === 0) {
                chordCtx.fillStyle = '#ffffff';
                chordCtx.font = 'bold 18px "SF Mono", monospace';
                chordCtx.fillText('○', sx, topY);
            } else if (fret === -1 || fret === null || fret === undefined) {
                chordCtx.fillStyle = '#ff6b8b';
                chordCtx.font = 'bold 24px "SF Mono", monospace';
                chordCtx.fillText('×', sx, topY);
            }

            if (typeof fret === 'number' && fret > 0 && fret <= 5) {
                const fretY = nutY + fret * fretSpacing - fretSpacing / 2;
                chordCtx.fillStyle = 'rgba(110, 231, 255, 0.95)';
                chordCtx.beginPath();
                chordCtx.arc(sx, fretY, 12, 0, Math.PI * 2);
                chordCtx.fill();
                chordCtx.fillStyle = '#08101c';
                chordCtx.font = 'bold 14px monospace';
                chordCtx.fillText(String(fret), sx, fretY);
            }
        }

        for (let i = 0; i < stringCount; i++) {
            const sx = diagX + i * stringSpacing;
            const finger = fingers[i];
            if (typeof finger === 'number' && finger >= 0) {
                chordCtx.fillStyle = 'rgba(255, 255, 255, 0.85)';
                chordCtx.font = '600 13px "SF Mono", monospace';
                chordCtx.fillText(String(finger), sx, nutY + diagHeight + 22);
            }
        }

        const lowestFret = Math.min(...frets.filter((f) => typeof f === 'number' && f > 0));
        if (isFinite(lowestFret) && lowestFret > 1) {
            chordCtx.font = '500 12px "SF Mono", monospace';
            chordCtx.fillStyle = 'rgba(255, 255, 255, 0.7)';
            chordCtx.textAlign = 'left';
            chordCtx.fillText(`${lowestFret}fr`, diagX - 32, nutY + fretSpacing * 2.5);
        }
    }

    function drawChordBoxes(now) {
        if (!chordCtx || !state.ready || !state.chords.length || !state.chordTemplates.length) return;
        const W = chordCanvas.clientWidth;
        const H = chordCanvas.clientHeight;

        chordCtx.clearRect(0, 0, chordCanvas.width, chordCanvas.height);
        chordCtx.fillStyle = 'rgba(6, 10, 18, 0.96)';
        chordCtx.fillRect(0, 0, W, H);

        const hitX = W * HIT_LINE_FRAC;
        const tMin = now - BEHIND;
        const tMax = now + AHEAD;
        const visible = [];
        for (const ch of state.chords) {
            if (ch.t < tMin) continue;
            if (ch.t > tMax) break;
            visible.push(ch);
        }
        if (!visible.length) return;

        // Deduplicate consecutive chords with the same name
        const unique = [];
        let lastChordName = null;
        for (const ch of visible) {
            const template = state.chordTemplates[ch.id];
            const chordName = template?.name || `Chord ${ch.id}`;
            if (chordName !== lastChordName) {
                unique.push(ch);
                lastChordName = chordName;
            }
        }

        const nStrings = (state.tuning && state.tuning.length === 4) ? 4 : 6;
        const diagWidth = 140;
        const diagHeight = 140;
        const boxPadding = 24;

        let activeIndex = -1;
        for (let i = 0; i < unique.length; i++) {
            if (unique[i].t <= now) activeIndex = i;
            else break;
        }
        if (activeIndex < 0) activeIndex = 0;
        const activeChord = unique[activeIndex];
        const otherChords = unique.filter((_, idx) => idx !== activeIndex).reverse();

        const renderChordBox = (ch, isCurrent) => {
            const x = isCurrent ? hitX : timeX(ch.t, now, W);
            if (x < -diagWidth - boxPadding) return;
            if (x > W + boxPadding) return;

            const template = state.chordTemplates[ch.id] || null;
            if (!template) return;

            const chordName = template.name || `Chord ${ch.id}`;
            const frets = template.frets || [];
            const fingers = template.fingers || [];

            // Calculate the minimum fret for positioning
            const playedFrets = frets.filter(f => typeof f === 'number' && f > 0);
            const minFret = playedFrets.length > 0 ? Math.min(...playedFrets) : 1;
            const maxFret = playedFrets.length > 0 ? Math.max(...playedFrets) : 1;

            // Ignore chord diagrams with names starting with "Chord " and those with only empty nodes
            if (chordName.startsWith('Chord ') || frets.every(f => f === 0 || f === -1 || f === null || f === undefined)) {
                return;
            }

            const stringCount = Math.min(nStrings, Math.max(4, frets.length));

            const boxLeft = x - diagWidth / 2;
            const boxTop = 12;

            const dt = now - ch.t;
            const fadeOutAfter = 0.22; // seconds after hit line before disappearing
            if (!isCurrent && (dt >= fadeOutAfter || boxLeft <= 0)) {
                return;
            }

            const approach = dt < 0
                ? 1 - Math.min(-dt, AHEAD) / AHEAD
                : Math.max(0, 1 - Math.min(dt, BEHIND) / BEHIND);

            const fillColor = isCurrent ? 'rgba(20, 30, 45, 1)' : 'rgba(18, 24, 34, 1)';
            const strokeColor = isCurrent
                ? 'rgba(110, 231, 255, 0.45)'
                : `rgba(140, 180, 230, ${0.18 + 0.2 * approach})`;
            const textColor = isCurrent
                ? '#ffffff'
                : `rgba(210, 220, 230, ${0.82 + 0.18 * approach})`;

            chordCtx.save();
            chordCtx.fillStyle = fillColor;
            roundRect(chordCtx, boxLeft - 8, boxTop - 8, diagWidth + 16, H - 16, 12);
            chordCtx.fill();

            chordCtx.strokeStyle = strokeColor;
            chordCtx.lineWidth = isCurrent ? 2 : 1.4;
            chordCtx.stroke();

            chordCtx.fillStyle = textColor;
            chordCtx.font = `${isCurrent ? 'bold ' : ''}14px "SF Mono", monospace`;
            chordCtx.textAlign = 'center';
            chordCtx.textBaseline = 'top';
            const displayName = minFret > 1 && maxFret > 5 ? `${chordName} (${minFret}fr)` : chordName;
            chordCtx.fillText(displayName, x, boxTop + 10);

            const diagY = boxTop + 40;
            const stringSpacing = diagWidth / Math.max(1, stringCount - 1);
            const fretSpacing = diagHeight / 5;
            const nutY = diagY;

            chordCtx.strokeStyle = 'rgba(200, 220, 255, 0.5)';
            chordCtx.lineWidth = 2;
            for (let i = 0; i < stringCount; i++) {
                const sx = x - diagWidth / 2 + i * stringSpacing;
                chordCtx.beginPath();
                chordCtx.moveTo(sx, nutY);
                chordCtx.lineTo(sx, nutY + diagHeight);
                chordCtx.stroke();
            }

            chordCtx.strokeStyle = 'rgba(180, 200, 240, 0.25)';
            chordCtx.lineWidth = 1;
            for (let f = 0; f <= 5; f++) {
                const fy = nutY + f * fretSpacing;
                chordCtx.beginPath();
                chordCtx.moveTo(x - diagWidth / 2, fy);
                chordCtx.lineTo(x + diagWidth / 2, fy);
                chordCtx.stroke();
            }

            chordCtx.strokeStyle = 'rgba(255, 255, 255, 0.8)';
            chordCtx.lineWidth = 3;
            chordCtx.beginPath();
            chordCtx.moveTo(x - diagWidth / 2, nutY);
            chordCtx.lineTo(x + diagWidth / 2, nutY);
            chordCtx.stroke();

            for (let i = 0; i < stringCount; i++) {
                const sx = x - diagWidth / 2 + i * stringSpacing;
                const fret = frets[i];
                const finger = fingers[i];
                const topY = nutY - 6;

                let relativeFret = null;
                if (typeof fret === 'number' && fret > 0) {
                    relativeFret = fret - minFret + 1;
                }

                chordCtx.textAlign = 'center';
                chordCtx.textBaseline = 'middle';

                if (fret === 0) {
                    chordCtx.fillStyle = '#ffffff';
                    chordCtx.font = 'bold 16px "SF Mono", monospace';
                    chordCtx.fillText('○', sx, topY);
                } else if (fret === -1 || fret === null || fret === undefined) {
                    chordCtx.fillStyle = '#ff6b8b';
                    chordCtx.font = 'bold 20px "SF Mono", monospace';
                    chordCtx.fillText('×', sx, topY);
                }

                if (relativeFret !== null && relativeFret <= 5) {
                    const fretY = nutY + relativeFret * fretSpacing - fretSpacing / 2;
                    chordCtx.fillStyle = 'rgba(110, 231, 255, 0.95)';
                    chordCtx.beginPath();
                    chordCtx.arc(sx, fretY, 10, 0, Math.PI * 2);
                    chordCtx.fill();
                    chordCtx.fillStyle = '#08101c';
                    chordCtx.font = 'bold 12px monospace';
                    chordCtx.fillText(String(relativeFret), sx, fretY);
                }

                if (typeof finger === 'number' && finger >= 0) {
                    chordCtx.fillStyle = 'rgba(255, 255, 255, 0.8)';
                    chordCtx.font = '600 11px "SF Mono", monospace';
                    chordCtx.fillText(String(finger), sx, nutY + diagHeight + 16);
                }
            }
            chordCtx.restore();
        };

        for (const ch of otherChords) {
            renderChordBox(ch, false);
        }
        renderChordBox(activeChord, true);
    }

    function drawNoteFrame(now) {
        if (!ctx || !noteCanvas) return;
        const W = noteCanvas.clientWidth;
        const H = noteCanvas.clientHeight;
        if (W === 0 || H === 0) return;
        const nStrings = (state.tuning && state.tuning.length === 4) ? 4 : 6;
        const colors = colorsFor(nStrings);

        drawBackground(W, H, nStrings, colors, now);
        drawSustains(W, H, nStrings, colors, now);
        // drawArcs (dashed trajectory curves) intentionally omitted — the
        // ball still hops along the underlying state.arcs data, we just
        // don't visualize the path.
        drawTechniquePairs(W, H, nStrings, colors, now);
        drawTechniqueArcs(W, H, nStrings, colors, now);
        drawNotes(W, H, nStrings, colors, now);
        drawBends(W, H, nStrings, colors, now);
        drawImpacts(W, H, nStrings, colors, now);
        drawBall(W, H, nStrings, colors, now);
        drawEdgeFade(W, H);
        drawStringLabels(W, H, nStrings, colors);
        drawHeader(W, H, now);
        drawProgress(W, H, now);
    }

    function drawChordFrame(now) {
        if (!chordCanvas || !chordCtx) return;
        drawChordBoxes(now);
    }

    function tick() {
        if (!active) return;
        const now = audioEl ? audioEl.currentTime : 0;
        drawNoteFrame(now);
        drawChordFrame(now);
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

    // Debug / demo-harness hook. Lets a standalone HTML page bind a
    // canvas, set synthetic state, and invoke drawFrame directly —
    // used by demo/ to generate screenshots without running slopsmith.
    window.__jumpingtab_demo = {
        setCanvas(cnv) {
            noteCanvas = cnv;
            chordCanvas = null;
            noteCtx = cnv.getContext('2d');
            ctx = noteCtx;
            const dpr = window.devicePixelRatio || 1;
            const rect = cnv.getBoundingClientRect();
            cnv.width = Math.max(1, Math.floor(rect.width * dpr));
            cnv.height = Math.max(1, Math.floor(rect.height * dpr));
            ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
        },
        setState(patch) { Object.assign(state, patch); },
        // Mirror the work that connect()'s finalize step does on real data
        // so demo states can be flat note arrays without precomputing.
        finalizeState() {
            state.notes.sort((a, b) => a.t - b.t);
            const lastIdxByString = new Map();
            const EPS_T = 1e-4;
            for (let i = 0; i < state.notes.length; i++) {
                const n = state.notes[i];
                n._gapL = Infinity;
                n._gapR = Infinity;
                const prevIdx = lastIdxByString.get(n.s);
                if (prevIdx != null) {
                    const prev = state.notes[prevIdx];
                    const gap = n.t - prev.t;
                    if (gap > EPS_T) {
                        n._gapL = gap;
                        if (gap < prev._gapR) prev._gapR = gap;
                    }
                }
                lastIdxByString.set(n.s, i);
            }
            state.arcs = buildTrajectories(state.notes);
            const tech = buildTechniqueArcs(state.notes);
            state.techArcs = tech.arcs;
            state.techPaired = tech.paired;
            state.ready = true;
        },
        drawFrame: drawNoteFrame,
        drawNoteFrame,
        drawChordFrame,
    };

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
