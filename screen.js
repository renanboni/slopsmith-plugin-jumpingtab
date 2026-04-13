(function () {
    'use strict';

    // ── Constants ─────────────────────────────────────────────
    const AHEAD = 2.8;
    const BEHIND = 0.4;
    const HIT_LINE_FRAC = 0.15;
    const FADE_SECONDS = 0.4;
    const SQUASH_WINDOW_MS = 50;
    const TOP_PAD = 24;
    const BOTTOM_PAD = 24;

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
        // Group notes by timestamp, preserving sort order.
        // A "group" with size > 1 is a chord and breaks arc continuity.
        if (notes.length < 2) return [];

        // Server rounds note times to 3 decimal places (ms precision), so
        // chord notes arrive with byte-identical floats. Use a small epsilon
        // anyway so any rounding drift upstream still groups them.
        const EPS = 1e-4;
        const groups = [];
        let i = 0;
        while (i < notes.length) {
            const t = notes[i].t;
            let j = i;
            while (j < notes.length && Math.abs(notes[j].t - t) < EPS) j++;
            groups.push({ t, notes: notes.slice(i, j) });
            i = j;
        }

        const arcs = [];
        for (let k = 0; k < groups.length - 1; k++) {
            const a = groups[k];
            const b = groups[k + 1];
            if (a.notes.length > 1 && b.notes.length > 1) continue;
            const n0 = a.notes[0];
            const n1 = b.notes[0];
            arcs.push({ t0: n0.t, t1: n1.t, s0: n0.s, f0: n0.f, s1: n1.s, f1: n1.f });
        }
        return arcs;
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
        ready: false,
        ws: null,
    };

    function connect(filename, arrangementIdx) {
        return new Promise((resolve, reject) => {
            // Close any prior socket
            if (state.ws) { try { state.ws.close(); } catch (e) {} state.ws = null; }
            state.filename = filename;
            state.tuning = null;
            state.notes = [];
            state.arcs = [];
            state.ready = false;

            const proto = location.protocol === 'https:' ? 'wss:' : 'ws:';
            const qs = (arrangementIdx != null && arrangementIdx >= 0)
                ? `?arrangement=${arrangementIdx}` : '';
            const url = `${proto}//${location.host}/ws/highway/${encodeURIComponent(filename)}${qs}`;
            const ws = new WebSocket(url);
            state.ws = ws;

            let total = null;

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
                    const mode = state.tuning.length === 4 ? 'bass (4)' : 'guitar (6)';
                    console.log('[jumpingtab] arrangement:', msg.arrangement, '— mode:', mode);
                } else if (msg.type === 'notes') {
                    total = msg.total;
                    for (const n of msg.data) state.notes.push(n);
                    if (!state.ready && total != null && state.notes.length >= total) {
                        state.notes.sort((a, b) => a.t - b.t);
                        state.arcs = buildTrajectories(state.notes);
                        state.ready = true;
                        resolve(state);
                        // Leave socket open for beat/lyric messages that may trail;
                        // close it on teardown or next playSong.
                    }
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
    let ctx = null;
    let raf = null;
    let audioEl = null;

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
        canvas = document.createElement('canvas');
        canvas.id = 'jumpingtab-canvas';
        // Insert the canvas as a flex sibling right after #highway, so it
        // gets the same flex slot as #highway (above #player-controls, below
        // #player-hud). Using flex: 1 + min-height: 0 mirrors #highway's
        // own rules in static/style.css, so the layout engine does the
        // sizing for us — no overlap with the controls or HUD.
        canvas.style.cssText = [
            'flex:1',
            'width:100%',
            'min-height:0',
            'display:block',
            'background:#0f1420',
        ].join(';');
        hw.insertAdjacentElement('afterend', canvas);
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
        if (canvas) { canvas.remove(); canvas = null; ctx = null; }
        const hw = document.getElementById('highway');
        if (hw) hw.style.display = '';
        audioEl = null;
    }

    // ── Renderer ─────────────────────────────────────────────
    function drawBackground(W, H, nStrings, colors) {
        ctx.fillStyle = '#0f1420';
        ctx.fillRect(0, 0, W, H);

        ctx.strokeStyle = '#3a4358';
        ctx.lineWidth = 1;
        for (let s = 0; s < nStrings; s++) {
            const y = stringY(s, H, nStrings);
            ctx.beginPath();
            ctx.moveTo(0, y);
            ctx.lineTo(W, y);
            ctx.stroke();
        }

        ctx.font = 'bold 11px monospace';
        ctx.textBaseline = 'middle';
        ctx.textAlign = 'left';
        const labels = nStrings === 4 ? ['G','D','A','E'] : ['e','B','G','D','A','E'];
        for (let s = 0; s < nStrings; s++) {
            ctx.fillStyle = colors[s];
            ctx.fillText(labels[s], 6, stringY(s, H, nStrings));
        }

        const hitX = W * HIT_LINE_FRAC;
        ctx.save();
        ctx.shadowColor = '#6ee7ff';
        ctx.shadowBlur = 16;
        ctx.strokeStyle = '#6ee7ff';
        ctx.lineWidth = 2;
        ctx.beginPath();
        ctx.moveTo(hitX, 8);
        ctx.lineTo(hitX, H - 8);
        ctx.stroke();
        ctx.restore();
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
            const y = stringY(n.s, H, nStrings);
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
        ctx.globalAlpha = 0.55;
        ctx.lineWidth = 2;
        ctx.setLineDash([4, 4]);

        for (const arc of state.arcs) {
            if (arc.t1 < lo || arc.t0 > hi) continue;
            if (arc.s0 < 0 || arc.s0 >= nStrings) continue;
            if (arc.s1 < 0 || arc.s1 >= nStrings) continue;
            const x0 = timeX(arc.t0, now, W);
            const y0 = stringY(arc.s0, H, nStrings);
            const x1 = timeX(arc.t1, now, W);
            const y1 = stringY(arc.s1, H, nStrings);
            const { cx, cy } = arcControlPoint(x0, y0, x1, y1);
            ctx.beginPath();
            ctx.moveTo(x0, y0);
            ctx.quadraticCurveTo(cx, cy, x1, y1);
            ctx.stroke();
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
        const y0 = stringY(arc.s0, H, nStrings);
        const x1 = timeX(arc.t1, now, W);
        const y1 = stringY(arc.s1, H, nStrings);
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
        ctx.fillStyle = '#ffffff';
        ctx.shadowColor = '#6ee7ff';
        ctx.shadowBlur = 14;
        ctx.translate(p.x, p.y);
        ctx.scale(sx, sy);
        ctx.beginPath();
        ctx.arc(0, 0, 8, 0, Math.PI * 2);
        ctx.fill();
        ctx.restore();
    }

    function drawNotes(W, H, nStrings, colors, now) {
        if (!state.ready || !state.notes.length) return;
        const { start, end } = binaryVisibleRange(state.notes, now);

        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';
        ctx.font = 'bold 11px monospace';

        for (let i = start; i < end; i++) {
            const n = state.notes[i];
            if (n.s < 0 || n.s >= nStrings) continue;
            const x = timeX(n.t, now, W);
            const y = stringY(n.s, H, nStrings);
            const color = colors[n.s];

            // Past-note fade: once x < hitX, fade over FADE_SECONDS of real time
            let alpha = 1;
            const dt = now - n.t;
            if (dt > 0) {
                alpha = 1 - (dt / FADE_SECONDS);
                if (alpha <= 0) continue;
            }

            ctx.save();
            ctx.globalAlpha = alpha;
            ctx.fillStyle = color;
            ctx.beginPath();
            ctx.arc(x, y, 12, 0, Math.PI * 2);
            ctx.fill();
            ctx.fillStyle = '#0f1420';
            ctx.fillText(String(n.f), x, y + 0.5);
            ctx.restore();
        }
    }

    function drawFrame(now) {
        if (!ctx || !canvas) return;
        // Draw in CSS pixels (ctx transform already scales to DPR).
        // canvas.clientWidth/Height reflect the layout-assigned size.
        const W = canvas.clientWidth;
        const H = canvas.clientHeight;
        if (W === 0 || H === 0) return;
        const nStrings = (state.tuning && state.tuning.length === 4) ? 4 : 6;
        const colors = colorsFor(nStrings);

        drawBackground(W, H, nStrings, colors);
        drawSustains(W, H, nStrings, colors, now);
        drawArcs(W, H, nStrings, colors, now);
        drawNotes(W, H, nStrings, colors, now);
        drawBall(W, H, nStrings, colors, now);
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

    console.log('[jumpingtab] plugin loaded');
})();
