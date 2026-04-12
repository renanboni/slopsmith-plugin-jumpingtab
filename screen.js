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

        const groups = [];
        let i = 0;
        while (i < notes.length) {
            const t = notes[i].t;
            let j = i;
            while (j < notes.length && notes[j].t === t) j++;
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

    console.log('[jumpingtab] plugin loaded');
})();
