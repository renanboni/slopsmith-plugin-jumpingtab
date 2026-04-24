// Jumping Tab visualization plugin — Yousician-style hopping-ball
// tablature view. A glowing ball hops along a parabolic trajectory
// from note to note on a 6-string (or 4-string bass) canvas tab.
//
// Wave B migration (slopsmith#36 path 1): the plugin used to open its
// own /ws/highway/{filename} WebSocket, parse song_info/notes/chords/
// beats/sections into module-scope state, then build trajectories on
// the client. It now consumes that same data from the setRenderer
// `bundle` passed to draw() — zero extra WebSockets, no custom route,
// difficulty-filter aware arrays. Trajectories still build
// client-side (this was always the case) but now from bundle input
// rather than from our own WS parse.
//
// Jumping Tab is arrangement-agnostic — it works on any song's
// arrangement — so no matchesArrangement is declared. Auto mode
// won't pick it automatically; users select it manually via the viz
// picker.
//
// Single-instance assumption: overlay canvas wrapper + chart caches
// live at module scope. The main-player picker uses one instance at
// a time. Splitscreen per-panel setRenderer adoption (Wave C) will
// re-factor into createFactory closures.

(function () {
    'use strict';

    // ── Constants ─────────────────────────────────────────────
    const AHEAD = 8.0;
    const BEHIND = 1.2;
    const HIT_LINE_FRAC = 0.18;
    const FADE_SECONDS = 1.0;
    const SQUASH_WINDOW_MS = 60;
    const IMPACT_DURATION = 0.45;
    const TOP_PAD = 60;
    const BOTTOM_PAD = 36;
    const HIT_ZONE_WIDTH = 56;
    const EDGE_FADE_FRAC = 0.06;
    const NOTE_BASE_R = 14;
    const NOTE_MAX_R = 18;
    const HEADER_H = 36;

    const GUITAR_COLORS = ['#ff6b8b', '#ffa56b', '#ffe66b', '#6bff95', '#6bd5ff', '#c56bff'];
    const BASS_COLORS   = ['#ff6b8b', '#ffe66b', '#6bff95', '#6bd5ff'];

    // ── Pure helpers (unchanged — test harness exercises these) ─────
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
        let l = 0, r = notes.length;
        while (l < r) {
            const m = (l + r) >> 1;
            if (notes[m].t < lo) l = m + 1; else r = m;
        }
        const start = l;
        l = start; r = notes.length;
        while (l < r) {
            const m = (l + r) >> 1;
            if (notes[m].t <= hi) l = m + 1; else r = m;
        }
        return { start, end: l };
    }

    function buildTrajectories(notes) {
        if (notes.length < 2) return [];
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

    function bendText(bn) {
        if (!bn || bn <= 0) return '';
        if (bn === 0.5) return '½';
        if (bn === 1) return 'full';
        if (bn === 1.5) return '1½';
        if (bn === 2) return '2';
        if (bn === 2.5) return '2½';
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

    // ── Module-level cached chart state (built from bundle) ──
    const state = {
        tuning: null,
        notes: [],
        arcs: [],
        techArcs: [],
        techPaired: new Set(),
        beats: [],
        sections: [],
        songInfo: {},
        ready: false,
    };
    // Reference-identity sentinels for cache invalidation. Core
    // creates a new array whenever the filtered chart rebuilds (new
    // song, arrangement change, or master-difficulty change flips
    // _filteredNotes), so reference-compare is a cheap, reliable
    // signal that we must rebuild trajectories + gaps.
    let _lastNotesRef = null;
    let _lastChordsRef = null;

    function buildTechniqueArcs(notes) {
        const arcs = [];
        const paired = new Set();
        const lastOnString = new Map();
        for (const n of notes) {
            const prev = lastOnString.get(n.s);
            if (prev) {
                let type = null;
                if (n.ho) type = 'h';
                else if (n.po) type = 'p';
                // Slide target fret is encoded as >= 0 for a real
                // slide and -1 (or null / undefined) for "no slide".
                // 0 is a legal target — a slide INTO an open string —
                // and _rebuildChart uses `sl ?? -1` to preserve it;
                // the old `n.sl && n.sl > 0` check contradicted that
                // by silently dropping slides-to-open.
                else if (n.sl != null && n.sl >= 0) type = 's';
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

    // Flatten bundle.notes + bundle.chords into the single sorted
    // array the rest of this module expects, then precompute
    // per-note same-string neighbor gaps (needed by drawNotes'
    // radius clamp). Mirrors the finalize() step from the old
    // WS path on connect(), minus the WS-only bookkeeping.
    function _rebuildChart(notes, chords) {
        const flat = [];
        if (Array.isArray(notes)) {
            // Clone rather than pushing the upstream note object
            // directly. The gap precomputation below sets _gapL /
            // _gapR as instance fields, which would mutate the
            // bundle.notes entries owned by slopsmith core and
            // visible to every other renderer sharing the same
            // array. It would also throw in strict mode against
            // any frozen / sealed note object. The shape mirrors
            // the chord-expansion branch below so later drawing
            // code doesn't branch on "where did this note come from".
            for (const n of notes) {
                flat.push({
                    t: n.t,
                    s: n.s,
                    f: n.f,
                    sus: n.sus || 0,
                    ho: n.ho || 0,
                    po: n.po || 0,
                    // `??` not `||` — `sl` (slide target fret) can
                    // legitimately be 0 (slide into an open string).
                    // `0 || -1` would collapse that to "no slide" and
                    // drawTechniqueArcs would stop drawing the slide
                    // indicator above those notes. sus / ho / po / bn
                    // use `||` safely because their falsy default and
                    // their no-op numeric value are the same (0).
                    sl: n.sl ?? -1,
                    bn: n.bn || 0,
                });
            }
        }
        if (Array.isArray(chords)) {
            for (const c of chords) {
                if (!c || !Array.isArray(c.notes)) continue;
                for (const cn of c.notes) {
                    flat.push({
                        t: c.t,
                        s: cn.s,
                        f: cn.f,
                        sus: cn.sus || 0,
                        ho: cn.ho || 0,
                        po: cn.po || 0,
                        sl: cn.sl ?? -1,  // see single-note branch above
                        bn: cn.bn || 0,
                    });
                }
            }
        }
        flat.sort((a, b) => a.t - b.t);

        const lastIdxByString = new Map();
        const EPS_T = 1e-4;
        for (let i = 0; i < flat.length; i++) {
            const n = flat[i];
            n._gapL = Infinity;
            n._gapR = Infinity;
            const prevIdx = lastIdxByString.get(n.s);
            if (prevIdx != null) {
                const prev = flat[prevIdx];
                const gap = n.t - prev.t;
                if (gap > EPS_T) {
                    n._gapL = gap;
                    if (gap < prev._gapR) prev._gapR = gap;
                }
            }
            lastIdxByString.set(n.s, i);
        }

        state.notes = flat;
        state.arcs = buildTrajectories(flat);
        const tech = buildTechniqueArcs(flat);
        state.techArcs = tech.arcs;
        state.techPaired = tech.paired;
        state.ready = flat.length > 0;
    }

    function _clearChart() {
        state.notes = [];
        state.arcs = [];
        state.techArcs = [];
        state.techPaired = new Set();
        state.beats = [];
        state.sections = [];
        state.songInfo = {};
        state.tuning = null;
        state.ready = false;
        _lastNotesRef = null;
        _lastChordsRef = null;
    }

    // ── Canvas lifecycle ─────────────────────────────────────
    let canvas = null;
    let wrap = null;
    let ctx = null;
    let highwayCanvas = null;
    let prevHighwayDisplay = '';

    function yFor(s, H, nStrings) {
        return stringY(nStrings - 1 - s, H, nStrings);
    }

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
        ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    }

    function mountCanvas(providedHighwayCanvas) {
        // We anchor our wrap via
        // providedHighwayCanvas.insertAdjacentElement('afterend', ...),
        // so the only DOM dependency is a canvas with a connected
        // parent. The prior `#player` lookup was never actually used
        // below and made init() fail in environments where the
        // enclosing container has a different id (splitscreen panels,
        // tests, hosts that rename the shell).
        if (!providedHighwayCanvas || !providedHighwayCanvas.parentNode) return false;

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
        providedHighwayCanvas.insertAdjacentElement('afterend', wrap);
        ctx = canvas.getContext('2d');
        if (!ctx) {
            // getContext('2d') can return null when the browser has
            // locked this canvas element to a different context type,
            // or when 2D support is disabled for the origin. Without
            // this guard init() would hide the highway canvas and
            // flip _isReady=true, then drawFrame would no-op against
            // the null ctx every rAF — leaving the player blank with
            // no recovery until the user picked a different viz. Tear
            // the overlay down, leave the highway visible as a
            // fallback, and signal failure up to init().
            console.warn('[jumpingtab] mountCanvas: getContext("2d") returned null; aborting');
            wrap.remove();
            wrap = null;
            canvas = null;
            return false;
        }

        highwayCanvas = providedHighwayCanvas;
        prevHighwayDisplay = providedHighwayCanvas.style.display;
        providedHighwayCanvas.style.display = 'none';
        sizeCanvasToBox();
        return true;
    }

    function unmountCanvas() {
        if (wrap) {
            wrap.remove();
            wrap = null;
            canvas = null;
            ctx = null;
        }
        if (highwayCanvas) {
            highwayCanvas.style.display = prevHighwayDisplay;
            highwayCanvas = null;
            prevHighwayDisplay = '';
        }
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
        ctx.fillStyle = '#070b18';
        ctx.fillRect(0, 0, W, H);

        const topBand = TOP_PAD;
        const botBand = H - BOTTOM_PAD;
        const laneH = botBand - topBand;

        const laneGrad = ctx.createLinearGradient(0, topBand, 0, botBand);
        laneGrad.addColorStop(0, '#0d1428');
        laneGrad.addColorStop(0.5, '#0a1024');
        laneGrad.addColorStop(1, '#0d1428');
        ctx.fillStyle = laneGrad;
        ctx.fillRect(0, topBand, W, laneH);

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

        const hitX = W * HIT_LINE_FRAC;
        const zoneL = hitX - HIT_ZONE_WIDTH / 2;
        const zoneR = hitX + HIT_ZONE_WIDTH / 2;
        const zoneGrad = ctx.createLinearGradient(zoneL, 0, zoneR, 0);
        zoneGrad.addColorStop(0, 'rgba(110, 231, 255, 0)');
        zoneGrad.addColorStop(0.5, 'rgba(110, 231, 255, 0.18)');
        zoneGrad.addColorStop(1, 'rgba(110, 231, 255, 0)');
        ctx.fillStyle = zoneGrad;
        ctx.fillRect(zoneL, topBand, HIT_ZONE_WIDTH, laneH);

        ctx.lineWidth = 1.5;
        for (let s = 0; s < nStrings; s++) {
            const y = yFor(s, H, nStrings);
            ctx.strokeStyle = colors[s] + '60';
            ctx.beginPath();
            ctx.moveTo(0, y);
            ctx.lineTo(W, y);
            ctx.stroke();
        }

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

    function drawHeader(W, H, now) {
        const info = state.songInfo || {};
        const sec = currentSection(state.sections, now);

        const hdrGrad = ctx.createLinearGradient(0, 0, 0, HEADER_H);
        hdrGrad.addColorStop(0, 'rgba(12, 16, 30, 0.95)');
        hdrGrad.addColorStop(1, 'rgba(12, 16, 30, 0.6)');
        ctx.fillStyle = hdrGrad;
        ctx.fillRect(0, 0, W, HEADER_H);

        ctx.font = '600 13px -apple-system, system-ui, sans-serif';
        ctx.textBaseline = 'middle';
        ctx.textAlign = 'left';
        ctx.fillStyle = '#e6ecff';
        const title = info.title || 'Unknown';
        ctx.fillText(title, 16, HEADER_H / 2);

        const titleW = ctx.measureText(title).width;
        ctx.font = '400 12px -apple-system, system-ui, sans-serif';
        ctx.fillStyle = 'rgba(200, 210, 230, 0.55)';
        if (info.artist) {
            ctx.fillText('· ' + info.artist, 16 + titleW + 8, HEADER_H / 2);
        }

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

    function drawProgress(W, H, now) {
        const duration = (state.songInfo && state.songInfo.duration) || 0;
        if (duration <= 0) return;

        const barY = H - 22;
        const barH = 6;
        const barX = 16;
        const barW = W - 32;

        ctx.fillStyle = 'rgba(200, 210, 230, 0.12)';
        if (ctx.roundRect) {
            ctx.beginPath();
            ctx.roundRect(barX, barY, barW, barH, barH / 2);
            ctx.fill();
        } else {
            ctx.fillRect(barX, barY, barW, barH);
        }

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

    function noteRadius(x, hitX, W) {
        const dxRight = Math.abs(x - hitX);
        const span = Math.max(hitX, W - hitX);
        const t = 1 - Math.min(1, dxRight / (span * 0.6));
        return NOTE_BASE_R + (NOTE_MAX_R - NOTE_BASE_R) * Math.max(0, t);
    }

    function secondsToPx(seconds, W) {
        const hitX = W * HIT_LINE_FRAC;
        return seconds * (W - hitX) / AHEAD;
    }

    const MIN_NOTE_R = 6;
    function clampByNeighbors(baseR, n, W) {
        const gap = Math.min(n._gapL || Infinity, n._gapR || Infinity);
        if (!isFinite(gap)) return baseR;
        const gapPx = secondsToPx(gap, W);
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

            const leftClamp = a.n0 ? clampByNeighbors(NOTE_BASE_R, a.n0, W) : NOTE_BASE_R;
            const rightClamp = a.n1 ? clampByNeighbors(NOTE_BASE_R, a.n1, W) : NOTE_BASE_R;
            const R = Math.min(leftClamp, rightClamp);
            ctx.font = 'bold ' + Math.round(R * 0.95) + 'px "SF Mono", Menlo, monospace';

            let alpha = 1;
            const dt = now - a.t1;
            if (dt > 0) {
                alpha = 1 - (dt / FADE_SECONDS);
                if (alpha <= 0) continue;
            }

            ctx.save();
            ctx.globalAlpha = alpha;

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
                ctx.moveTo(left + R, top);
                ctx.lineTo(left + width - R, top);
                ctx.arc(left + width - R, y, R, -Math.PI / 2, Math.PI / 2);
                ctx.lineTo(left + R, top + height);
                ctx.arc(left + R, y, R, Math.PI / 2, (3 * Math.PI) / 2);
                ctx.closePath();
            }
            ctx.fill();

            ctx.shadowBlur = 0;
            ctx.lineWidth = 2;
            ctx.strokeStyle = 'rgba(255, 255, 255, 0.85)';
            ctx.stroke();

            ctx.fillStyle = '#0a0f1c';
            ctx.fillText(String(a.f0), x0, y + 1);
            ctx.fillText(String(a.f1), x1, y + 1);

            ctx.restore();
        }
    }

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
            if (x1 - x0 < 6) continue;
            const y = yFor(a.s, H, nStrings);
            const lift = 20;
            const cx = (x0 + x1) / 2;
            const cy = y - lift;

            const color = a.type === 'h' ? '#ffc86b'
                        : a.type === 'p' ? '#ff8ab6'
                        : '#ffffff';
            ctx.strokeStyle = color;
            ctx.globalAlpha = 0.85;
            ctx.beginPath();
            ctx.moveTo(x0, y - 4);
            ctx.quadraticCurveTo(cx, cy, x1, y - 4);
            ctx.stroke();

            ctx.globalAlpha = 1;
            ctx.fillStyle = color;
            ctx.fillText(a.type, cx, cy + 1);
        }

        ctx.restore();
    }

    function findActiveArc(arcs, now) {
        let best = null;
        for (const a of arcs) {
            if (a.t0 <= now && now <= a.t1) return a;
            if (a.t1 < now && (!best || a.t1 > best.t1)) best = a;
        }
        return best;
    }

    function nearestNoteAtHit(notes, now, hitX, W) {
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

        const hitX = W * HIT_LINE_FRAC;
        const nearest = nearestNoteAtHit(state.notes, now, hitX, W);
        let sx = 1, sy = 1;
        if (nearest && nearest.dx < 14) {
            const msFromNote = Math.abs(now - nearest.note.t) * 1000;
            if (msFromNote < SQUASH_WINDOW_MS) {
                const k = 1 - (msFromNote / SQUASH_WINDOW_MS);
                sx = 1 + 0.25 * k;
                sy = 1 - 0.40 * k;
            }
        }

        ctx.save();
        ctx.shadowColor = '#6ee7ff';
        ctx.shadowBlur = 18;
        ctx.translate(p.x, p.y);
        ctx.scale(sx, sy);
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

    function drawImpacts(W, H, nStrings, colors, now) {
        if (!state.ready || !state.notes.length) return;
        const { start, end } = binaryVisibleRange(state.notes, now);
        const hitX = W * HIT_LINE_FRAC;

        for (let i = start; i < end; i++) {
            const n = state.notes[i];
            if (n.s < 0 || n.s >= nStrings) continue;
            const dt = now - n.t;
            if (dt < 0 || dt >= IMPACT_DURATION) continue;

            const p = dt / IMPACT_DURATION;
            const ease = 1 - Math.pow(1 - p, 2);
            const y = yFor(n.s, H, nStrings);
            const color = colors[n.s];

            const baseR = 14;
            const r = baseR * (1 + ease * 2.2);
            const alpha = (1 - p) * 0.85;

            ctx.save();
            ctx.globalAlpha = alpha;
            ctx.strokeStyle = color;
            ctx.lineWidth = 3 - ease * 2;
            ctx.shadowColor = color;
            ctx.shadowBlur = 18;
            ctx.beginPath();
            ctx.arc(hitX, y, r, 0, Math.PI * 2);
            ctx.stroke();

            if (p < 0.5) {
                ctx.globalAlpha = (1 - p * 2) * 0.6;
                ctx.strokeStyle = '#ffffff';
                ctx.shadowBlur = 10;
                ctx.lineWidth = 2;
                ctx.beginPath();
                ctx.arc(hitX, y, baseR * (1 + ease * 1.2), 0, Math.PI * 2);
                ctx.stroke();
            }

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

            let alpha = 1;
            const dt = now - n.t;
            if (dt > 0) {
                alpha = 1 - (dt / FADE_SECONDS);
                if (alpha <= 0) continue;
            }

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

            ctx.beginPath();
            ctx.moveTo(x, baseY);
            ctx.lineTo(x, tipY + headH);
            ctx.stroke();

            ctx.shadowBlur = 0;
            ctx.beginPath();
            ctx.moveTo(x, tipY);
            ctx.lineTo(x - headW, tipY + headH);
            ctx.lineTo(x + headW, tipY + headH);
            ctx.closePath();
            ctx.fill();

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
            const R = clampByNeighbors(noteRadius(x, hitX, W), n, W);

            let alpha = 1;
            const dt = now - n.t;
            if (dt > 0) {
                alpha = 1 - (dt / FADE_SECONDS);
                if (alpha <= 0) continue;
            }

            ctx.save();
            ctx.globalAlpha = alpha;

            ctx.shadowColor = color;
            ctx.shadowBlur = 14;
            ctx.fillStyle = color;
            ctx.beginPath();
            ctx.arc(x, y, R, 0, Math.PI * 2);
            ctx.fill();

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

            ctx.lineWidth = 2;
            ctx.strokeStyle = 'rgba(255, 255, 255, 0.9)';
            ctx.beginPath();
            ctx.arc(x, y, R, 0, Math.PI * 2);
            ctx.stroke();

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
        // drawArcs (dashed trajectory curves) intentionally omitted —
        // the ball still hops along state.arcs; we just don't
        // visualize the path.
        drawTechniquePairs(W, H, nStrings, colors, now);
        drawTechniqueArcs(W, H, nStrings, colors, now);
        drawNotes(W, H, nStrings, colors, now);
        drawBends(W, H, nStrings, colors, now);
        drawImpacts(W, H, nStrings, colors, now);
        drawBall(W, H, nStrings, colors, now);
        drawEdgeFade(W, H);
        drawHeader(W, H, now);
        drawProgress(W, H, now);
    }

    // Debug / demo-harness hook preserved from the pre-migration
    // version — the standalone demo/ HTML binds a canvas, sets
    // synthetic state, and invokes drawFrame directly. Used to
    // generate README screenshots without running slopsmith.
    window.__jumpingtab_state = state;
    window.__jumpingtab_demo = {
        setCanvas(cnv) {
            canvas = cnv;
            ctx = cnv.getContext('2d');
            const dpr = window.devicePixelRatio || 1;
            const rect = cnv.getBoundingClientRect();
            cnv.width = Math.max(1, Math.floor(rect.width * dpr));
            cnv.height = Math.max(1, Math.floor(rect.height * dpr));
            ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
        },
        setState(patch) { Object.assign(state, patch); },
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
        drawFrame,
    };

    // ── Factory — slopsmith#36 setRenderer contract ────────────
    function createFactory() {
        let _isReady = false;
        const _onWinResize = () => sizeCanvasToBox();

        return {
            init(providedCanvas /* , bundle */) {
                // Defensive teardown mirrors destroy() exactly —
                // including restoreCanvas=true. If we skipped the
                // window.resize listener removal, a double init()
                // would leak a second listener; every resize would
                // fire sizeCanvasToBox twice. And if we skipped the
                // highway canvas restore, a later init() against a
                // different canvas (or the same element after a
                // teardown/remount cycle) would leave the previous
                // highwayCanvas display:none forever.
                if (wrap || _isReady) {
                    window.removeEventListener('resize', _onWinResize);
                    _teardown();
                    _isReady = false;
                    // _teardown already called _clearChart() — don't
                    // fire a second redundant reset on this branch.
                } else {
                    _clearChart();
                }
                if (!mountCanvas(providedCanvas)) {
                    console.warn('[jumpingtab] init: failed to mount overlay canvas');
                    return;
                }
                window.addEventListener('resize', _onWinResize);
                _isReady = true;
            },
            draw(bundle) {
                if (!_isReady || !ctx || !canvas || !bundle) return;

                // Pick up metadata cheaply each frame. Mutate the
                // existing state.songInfo object instead of
                // allocating a fresh one every frame — at 60fps
                // that's 60 short-lived metadata objects per second
                // of GC churn. Draw code only reads the four named
                // fields below; nothing holds a reference to a
                // specific per-frame snapshot.
                const info = bundle.songInfo || {};
                const si = state.songInfo || (state.songInfo = {});
                si.title = info.title || '';
                si.artist = info.artist || '';
                si.arrangement = info.arrangement || '';
                si.duration = info.duration || 0;
                // Always overwrite tuning, even when info.tuning is
                // missing. Without this reset, a bass song's 4-string
                // tuning from the previous arrangement would linger
                // into a guitar arrangement whose bundle omitted the
                // field, and drawFrame's nStrings check would still
                // return 4. null is harmless — nStrings falls back
                // to the guitar (6) default.
                state.tuning = Array.isArray(info.tuning) ? info.tuning : null;

                // Beats / sections track bundle references (same
                // identity-swap semantics as notes / chords). Always
                // overwrite rather than conditionally assign so a
                // bundle that omits or nulls either field during a
                // song-change loading window can't leave the PREVIOUS
                // song's timing grid visible in the background —
                // drawBackground would happily render last song's
                // measure lines / section bands against the new
                // song's notes otherwise.
                state.beats = Array.isArray(bundle.beats) ? bundle.beats : [];
                state.sections = Array.isArray(bundle.sections) ? bundle.sections : [];

                // Rebuild trajectories only when the underlying
                // chart arrays changed — either new song / arrangement
                // or a master-difficulty swap in slopsmith core's
                // _filteredNotes. Reference equality is enough
                // because core reassigns (not mutates) on every
                // filter rebuild.
                if (bundle.notes !== _lastNotesRef || bundle.chords !== _lastChordsRef) {
                    _lastNotesRef = bundle.notes;
                    _lastChordsRef = bundle.chords;
                    _rebuildChart(bundle.notes, bundle.chords);
                }

                drawFrame(bundle.currentTime || 0);
            },
            resize(/* w, h */) {
                // Size from the canvas's own bounding rect — the w/h
                // that highway.js hands over are scaled by its own
                // render-scale for the renderer that owns the given
                // #highway canvas, not our overlay.
                if (!_isReady) return;
                sizeCanvasToBox();
            },
            destroy() {
                _isReady = false;
                window.removeEventListener('resize', _onWinResize);
                _teardown();
            },
        };

        function _teardown() {
            unmountCanvas();
            _clearChart();
        }
    }

    window.slopsmithViz_jumpingtab = createFactory;

    console.log('[jumpingtab] plugin loaded (viz mode)');
})();
