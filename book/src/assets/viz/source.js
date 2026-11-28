// The source unfolding and the star unfolding of a small convex polyhedron,
// computed in the browser.
// Options: { "solid": "cube", "unfolding": "source" | "star" }.

import { SOLIDS, apply, dist, fold, foldedPath, frontier, inverse, locate, norm, polygonArea, sourceUnfolding, starUnfolding, sub } from './geom.js';
import { createView, drawSolid, faceColor, pick, pts, svg } from './view3d.js';
import { fmt, frame, h, row, select } from './ui.js';

const TEXT = {
  source: {
    title: 'Source unfolding',
    help: 'Drag the solid to rotate it. Click a face, or drag the source point, to move the source. Move the pointer over the net to see a radial segment and the path it folds to. Computed in JavaScript as an illustration; not checked by Lean.',
  },
  star: {
    title: 'Star unfolding',
    help: 'Drag the solid to rotate it. Click a face, or drag the source point, to move the source. The surface is cut along the orange shortest paths from the source to the vertices; the dashed lines are the cut locus. Move the pointer over the net to see the segment from the nearest image of the source and the path it folds to. Computed in JavaScript as an illustration; not checked by Lean.',
  },
};

export default function mount(root, cfg) {
  let mode = cfg.unfolding === 'star' ? 'star' : 'source';
  const ui = frame(root, TEXT[mode]);
  const title = root.querySelector('.viz-title');
  let kind = SOLIDS[cfg.solid] ? cfg.solid : 'cube';
  let mesh, source, U, edge, L, hover = null;
  const W = 380;
  const net = svg('svg', { viewBox: `${-W / 2} ${-W / 2} ${W} ${W}`, width: W, height: W, class: 'netview', role: 'img' });

  const sourcePoint = () => {
    const v = mesh.vertex[source.face];
    return [0, 1].map((k) => source.bary[0] * v[0][k] + source.bary[1] * v[1][k] + source.bary[2] * v[2][k]);
  };
  const clampBary = (b) => {
    const c = b.map((x) => Math.max(0.03, x));
    const s = c[0] + c[1] + c[2];
    return c.map((x) => x / s);
  };

  // Moving the source recomputes everything; do it at most once per frame.
  let pending = null;
  const moveSource = (p) => {
    if (!p) return;
    if (!pending) requestAnimationFrame(() => { const q = pending; pending = null; setSource(q); });
    pending = p;
  };
  const view = createView({
    draw: drawSpace,
    onPress: (ev) => ev.target.classList?.contains('v3-source'),
    onDrag: (at) => moveSource(pick(view, mesh, at)),
    onClick: (at) => moveSource(pick(view, mesh, at)),
  });
  ui.stage.append(h('div', { class: 'viz-pair' }, view.el, net));
  ui.controls.append(
    select(Object.entries(SOLIDS).map(([k, s]) => [k, s.label]), kind, (k) => { kind = k; reset(); }, { 'aria-label': 'solid' }),
    select([['source', 'source unfolding'], ['star', 'star unfolding']], mode, (m) => {
      mode = m;
      title.textContent = TEXT[mode].title;
      ui.help.textContent = TEXT[mode].help;
      setSource(source);
    }, { 'aria-label': 'unfolding' }),
  );

  function reset() {
    mesh = SOLIDS[kind].make();
    // Start on the face that looks most directly at the viewer.
    let face = 0;
    mesh.frames.forEach((fr, f) => { if (view.project(fr.n)[2] > view.project(mesh.frames[face].n)[2]) face = f; });
    setSource({ face, bary: [0.5, 0.2, 0.3] });
  }

  /**
   * What the net shows, in either mode:
   *   polys    convex pieces { pts, tags, piece }
   *   cuts     segments of the outline, where the surface is cut
   *   ridge    in the star unfolding, the cut locus, which is not cut
   *   sources  the images of the source
   *   paths    on the solid, the folded cuts: lists of points with their faces
   *   at(z)    the piece under a point of the net, the point z0 of the source
   *            unfolding that it stands for, and the image of the source it is seen from
   */
  function layoutSource() {
    return {
      polys: U.fragments.map((f) => ({ pts: f.poly.pts, tags: f.poly.tags, piece: f.piece })),
      cuts: edge.map((e) => [e.a, e.b]),
      ridge: [],
      sources: [[0, 0]],
      at: (z) => { const f = locate(U.fragments, z); return f && { piece: f.piece, z0: z, from: [0, 0] }; },
    };
  }
  function layoutStar() {
    const S = starUnfolding(mesh, U, edge);
    if (!S.complete) return null;
    return {
      polys: S.parts.map((p) => ({ pts: p.flat.pts, tags: p.flat.tags, piece: p.piece })),
      cuts: S.outline.map((a, k) => [a, S.outline[(k + 1) % S.outline.length]]),
      ridge: S.ridge,
      sources: S.wedges.map((w) => w.apex),
      paths: S.images.map((im) => foldedPath(mesh, im.fragment, im.z)),
      at: (z) => {
        const p = locate(S.parts, z, 'flat');
        const w = p && S.wedges[p.wedge];
        return p && { piece: p.piece, z0: apply(inverse(w.M), z), from: w.apex };
      },
    };
  }

  function setSource(p) {
    source = { face: p.face, bary: clampBary(p.bary) };
    U = sourceUnfolding(mesh, source.face, sourcePoint());
    edge = frontier(U.fragments);
    L = (mode === 'star' && layoutStar()) || layoutSource();
    L.star = mode === 'star' && L.ridge.length > 0;
    hover = null;
    drawNet();
    drawSpace();
    drawState();
  }

  function drawSpace() {
    const { back, front } = drawSolid(view, mesh);
    const cutBack = svg('g'), cutFront = svg('g');
    const line = (A, B, face, cls) => {
      const a = view.project(A), b = view.project(B);
      const isFront = view.facing(mesh.frames[face].n);
      (isFront ? cutFront : cutBack).append(svg('line', { x1: a[0], y1: a[1], x2: b[0], y2: b[1], class: `${cls}${isFront ? '' : ' hidden'}` }));
    };
    // The cut locus: cut in the source unfolding, only drawn in the star unfolding.
    for (const e of edge) line(fold(mesh, e.fragment, e.a), fold(mesh, e.fragment, e.b), e.fragment.piece.face, L.star ? 'ridge' : 'cut');
    if (L.star) for (const path of L.paths) for (let k = 0; k + 1 < path.length; k++) line(path[k], path[k + 1], path.faces[k], 'cut');
    const s = view.project(mesh.place(source.face, sourcePoint()));
    const sFront = view.facing(mesh.frames[source.face].n);
    const marker = svg('circle', { cx: s[0], cy: s[1], r: 6, class: `v3-source${sFront ? '' : ' hidden'}` });
    const path = svg('g');
    if (hover) {
      const p = foldedPath(mesh, hover, hover.z0).map(view.project);
      path.append(svg('polyline', { points: pts(p), class: 'geodesic' }));
      const end = p[p.length - 1];
      path.append(svg('circle', { cx: end[0], cy: end[1], r: 3.5, class: 'geodesic-end' }));
    }
    view.el.replaceChildren(back, cutBack, front, cutFront, path, marker);
  }

  // The net is drawn centred on `centre`, at `k` pixels per unit.
  let k = 1, centre = [0, 0];
  const at = (p) => [(p[0] - centre[0]) * k, -(p[1] - centre[1]) * k];
  function drawNet() {
    const all = L.polys.flatMap((p) => p.pts);
    if (L.star) {
      const xs = all.map((p) => p[0]), ys = all.map((p) => p[1]);
      centre = [(Math.min(...xs) + Math.max(...xs)) / 2, (Math.min(...ys) + Math.max(...ys)) / 2];
    } else centre = [0, 0];
    k = (W / 2 - 10) / Math.max(...all.map((p) => Math.max(Math.abs(p[0] - centre[0]), Math.abs(p[1] - centre[1]))));
    if (!L.star) k = (W / 2 - 10) / Math.max(...all.map(norm));
    const fill = svg('g'), seams = svg('g'), ridge = svg('g'), cut = svg('g'), dots = svg('g');
    const segment = (group, [a, b], cls) => {
      const p = at(a), q = at(b);
      group.append(svg('line', { x1: p[0], y1: p[1], x2: q[0], y2: q[1], class: cls }));
    };
    for (const poly of L.polys) {
      const colour = faceColor(mesh.groups[poly.piece.face]);
      fill.append(svg('polygon', { points: pts(poly.pts.map(at)), fill: colour, 'fill-opacity': 0.5, stroke: colour, 'stroke-opacity': 0.5, 'stroke-width': 0.6 }));
      poly.pts.forEach((p, i) => { if (poly.tags[i] === 'seam') segment(seams, [p, poly.pts[(i + 1) % poly.pts.length]], 'net-seam'); });
    }
    for (const e of L.ridge) segment(ridge, e, 'ridge');
    for (const e of L.cuts) segment(cut, e, 'cut');
    for (const s of L.sources) {
      const p = at(s);
      dots.append(svg('circle', { cx: p[0], cy: p[1], r: L.star ? 3.5 : 5, class: L.star ? 'source-image' : 'v3-source still' }));
    }
    const radial = svg('g', { class: 'radial' });
    net.replaceChildren(fill, seams, ridge, cut, radial, dots);
    // Many cuts: draw them thinner, here and on the solid.
    for (const el of [net, view.el]) el.classList.toggle('dense', L.star && L.cuts.length > 60);
    net.radial = radial;
  }
  const netPoint = (ev) => {
    const box = net.getBoundingClientRect();
    return [((ev.clientX - box.left) * W / box.width - W / 2) / k + centre[0], -((ev.clientY - box.top) * W / box.height - W / 2) / k + centre[1]];
  };
  net.addEventListener('pointermove', (ev) => {
    const z = netPoint(ev);
    const found = L.at(z);
    hover = found ? { ...found, z } : null;
    net.radial.replaceChildren();
    if (hover) {
      const a = at(hover.from), b = at(z);
      net.radial.append(svg('line', { x1: a[0], y1: a[1], x2: b[0], y2: b[1], class: 'geodesic' }),
        svg('circle', { cx: b[0], cy: b[1], r: 3.5, class: 'geodesic-end' }));
    }
    drawSpace();
    drawState();
  });
  net.addEventListener('pointerleave', () => { hover = null; net.radial.replaceChildren(); drawSpace(); drawState(); });

  function drawState() {
    const area = L.polys.reduce((s, p) => s + polygonArea(p.pts), 0);
    const length = L.star ? 'distance to the nearest image = distance on the surface' : '‖z‖ = distance on the surface';
    const straight = () => dist(fold(mesh, hover, hover.z0), mesh.place(source.face, sourcePoint()));
    ui.state.replaceChildren(
      row('area of the net', `${fmt(area, 4)} &nbsp;(surface: ${fmt(mesh.area(), 4)})`),
      L.star
        ? row('outline', `${L.cuts.length} sides: ${L.sources.length} vertices alternate with ${L.sources.length} images of the source`)
        : row('pieces', `${new Set(L.polys.map((p) => p.piece)).size} polygons, each folded by one rigid motion`),
      hover
        ? row(length, `${fmt(norm(sub(hover.z, hover.from)), 4)} &nbsp;(straight through the solid: ${fmt(straight(), 4)})`)
        : row(length, '<em>point at the net</em>'),
    );
  }
  reset();
}
