# Jumping Tab

A [slopsmith](https://github.com/byrongamatos/slopsmith) plugin that adds a Yousician-style 2D horizontal tab view to the player. Notes flow right-to-left toward a glowing hit line, trajectory arcs connect consecutive monophonic notes, a glowing ball visibly hops along those arcs, and chord-shape diagrams scroll along a secondary canvas above the tab.

![Chord boxes + tab view](screenshots/jumpingtab_w_chords.png)

## Features

- **2D horizontal tab** — notes scroll right→left on color-coded string lines, player view (low E on top), Rocksmith-aligned color palette.
- **Chord-shape diagrams** — a secondary canvas above the tab renders the active chord shape (open / muted / fingered strings, fret numbers, finger numbers, position label) and queues upcoming distinct chord shapes scrolling toward the hit line. Distinguishes consecutive identical chords so a held shape doesn't draw N times. *(Originally contributed by [alleexx](https://github.com/alleexx) on the [renanboni fork](https://github.com/renanboni/slopsmith-plugin-jumpingtab).)*
- **Trajectory arcs** — dashed cyan curves connect every consecutive note group (chords included) so you can see the melodic contour.
- **Hopping ball** — a glowing ball traces the melody and squashes when it crosses the hit line.
- **Technique rendering** — hammer-ons, pull-offs, and slides are drawn as fused capsules with labeled arcs above them; bends get amber arrows with conventional labels (`½`, `full`, `1½`, `2`).
- **Section bands** — the current song section (intro / verse / chorus / solo / outro) is highlighted behind the notes and shown in a badge in the header.
- **Beat & measure ticks** under the notes so you can feel the rhythm grid.
- **Density-aware sizing** — notes shrink automatically in fast passages so adjacent fret circles never overlap, with a visual gutter between them.
- **Progress bar** along the bottom with `mm:ss` timestamps.
- **Dynamic string count** — uses slopsmith core's `bundle.stringCount` (slopsmith-plugin-3dhighway#7) so 4-string bass renders 4 lanes, 6-string guitar renders 6, and extended-range 7- and 8-string GP imports render their full string count without spillover.
- **Splitscreen multi-instance** — N panels under splitscreen each get their own factory instance with independent chord-box rendering, trajectory caches, and visual state.
- **Respects arrangement switching** — swapping Lead / Rhythm / Bass in the slopsmith player dropdown rebuilds the tab and chord data live.

### Techniques showcase

![Hammer-ons, pull-offs, bends, and a chord landing](screenshots/techniques.png)

The capsule shape on the left is a hammer-on pair (`5`→`7`), the pill after it is a pull-off. Amber arrows with labels show the bend size on each bent note. The chord on the right is rendered as a vertical stack of fret circles, and the preceding trajectory arc lands at the chord's centroid.

### Fast passages

![Dense sixteenth-note run](screenshots/fast.png)

At 120 BPM sixteenth notes, the per-note radius clamps to half the same-string neighbor gap so every circle stays distinct instead of blurring into one blob.

## Install

Clone into your slopsmith `plugins/` directory and restart the web service:

```bash
cd /path/to/slopsmith/plugins
git clone https://github.com/renanboni/slopsmith-plugin-jumpingtab.git jumpingtab
cd ..
docker compose restart web
```

Hard-reload the browser. **Jumping Tab** appears in the main-player visualization picker (top-right of the player controls), and in each per-panel picker under splitscreen.

## Architecture

This plugin implements slopsmith core's `setRenderer` contract (slopsmith#36), so it's a full-replacement renderer rather than a toggle overlay. The Wave C per-instance refactor means N splitscreen panels can each pick **Jumping Tab** independently with their own state.

Because Jumping Tab is arrangement-agnostic — it works on any tuning / arrangement — it doesn't declare `matchesArrangement`, so **Auto** mode won't pick it automatically; you select it manually from the picker.

## Use

1. Pick a song from your library.
2. Open the visualization picker in the player controls and choose **Jumping Tab**.
3. Press play. Watch the ball hop and the chord shapes scroll.
4. Switch back by picking **Highway** (or any other viz) in the picker.

Arrangement changes (Lead → Rhythm → Bass via the player dropdown) and difficulty-slider moves are detected automatically — the tab and chord data rebuild in place while Jumping Tab stays selected.

## Visual style

The current visual identity merges contributions from multiple authors:

- **alleexx** ([renanboni fork](https://github.com/renanboni/slopsmith-plugin-jumpingtab)): chord-box rendering, Rocksmith-aligned string color palette (string 0 = pink, string 1 = yellow, string 2 = cyan, etc.), and reduced hit-line glow (`DISABLE_RINGS = true` opts out of the expanding-ring animation that was visually busy in dense passages).
- **byrongamatos**: setRenderer + Wave C per-instance architecture, technique capsules, bend indicators, trajectory hopping ball, dynamic string count.
- **topkoa**: contributed the original splitscreen-pane factory in the renanboni fork; superseded by Wave C's per-panel viz picker which made a separate pane contract unnecessary.
- **rymarshall**: contributed a WebSocket URL encoding fix in the renanboni fork; obsoleted by the setRenderer migration which moved WebSocket ownership to slopsmith core.

## What it doesn't do (yet)

- No microphone input or scoring.
- No settings panel for speed / colors / visibility window.
- No standalone full-screen mode — it's a player overlay.

## Tests

`test/test.html` is a zero-dependency browser test harness for the pure helpers (layout math, binary search, trajectory builder, bezier, color-palette switching). Open the file directly:

```
file:///path/to/jumpingtab/test/test.html
```

The page title shows `N pass / 0 fail`. Rendering, animation, and plugin integration are verified manually.

## Demo harness

`demo/index.html` is a standalone page that loads `screen.js` with synthetic data and renders a static frame — no slopsmith instance required. It was used to generate the screenshots in this README. Switch scenes with a query string:

```
file:///path/to/jumpingtab/demo/index.html?scene=overview
file:///path/to/jumpingtab/demo/index.html?scene=techniques
file:///path/to/jumpingtab/demo/index.html?scene=fast
```

To regenerate the screenshots yourself:

```bash
CHROME="/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"
for scene in overview techniques fast; do
  "$CHROME" --headless=new --disable-gpu --hide-scrollbars \
    --window-size=1344,484 \
    --screenshot="screenshots/${scene}.png" \
    "file://$(pwd)/demo/index.html?scene=${scene}"
done
```
