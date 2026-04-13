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

    function sizeCanvasToHighway() {
        const hw = document.getElementById('highway');
        if (!hw || !canvas) return;
        const w = hw.width || hw.clientWidth;
        const h = hw.height || hw.clientHeight;
        canvas.width = w;
        canvas.height = h;
        canvas.style.width = hw.style.width || (w + 'px');
        canvas.style.height = hw.style.height || (h + 'px');
    }

    function mountCanvas() {
        const player = document.getElementById('player');
        const hw = document.getElementById('highway');
        if (!player || !hw) return false;
        canvas = document.createElement('canvas');
        canvas.id = 'jumpingtab-canvas';
        // Match tabview's mount pattern: append to #player, absolutely positioned
        // at 0,0, sized to match #highway. This assumes #player is the positioned
        // ancestor (which tabview relies on and is already proven to work).
        canvas.style.cssText = [
            'position:absolute',
            'left:0',
            'top:0',
            'z-index:5',
            'pointer-events:none',
        ].join(';');
        player.appendChild(canvas);
        ctx = canvas.getContext('2d');
        sizeCanvasToHighway();
        hw.style.display = 'none';
        audioEl = document.querySelector('audio');
        window.addEventListener('resize', sizeCanvasToHighway);
        return true;
    }

    function unmountCanvas() {
        if (raf) { cancelAnimationFrame(raf); raf = null; }
        window.removeEventListener('resize', sizeCanvasToHighway);
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
        const W = canvas.width, H = canvas.height;
        const nStrings = (state.tuning && state.tuning.length === 4) ? 4 : 6;
        const colors = colorsFor(nStrings);

        drawBackground(W, H, nStrings, colors);
        drawSustains(W, H, nStrings, colors, now);
        drawNotes(W, H, nStrings, colors, now);
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
        b.onclick = toggle;
        c.insertBefore(b, last);
    }

    // Expose for manual poking / future tests
    window.__jumpingtab_state = state;
    window.__jumpingtab_connect = connect;

    // ── Hook installation ────────────────────────────────────
    const _origPlay = window.playSong;
    window.playSong = async function (filename, arrangement) {
        await _origPlay(filename, arrangement);
        injectBtn();
        try {
            await connect(filename, arrangement);
            console.log('[jumpingtab] loaded',
                state.notes.length, 'notes,', state.arcs.length, 'arcs,',
                'tuning', state.tuning);
        } catch (e) {
            console.warn('[jumpingtab] connect failed:', e.message);
        }
    };

    const _origShow = window.showScreen;
    window.showScreen = function (id) {
        if (id !== 'player' && active) {
            active = false;
            unmountCanvas();
        }
        if (typeof _origShow === 'function') _origShow(id);
    };

    console.log('[jumpingtab] plugin loaded');
})();
