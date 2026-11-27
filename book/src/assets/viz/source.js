// The source unfolding of a small convex polyhedron, computed in the browser.
// Options: { "solid": "cube" }.

import { SOLIDS, add, dist, fold, foldedPath, frontier, locate, norm, polygonArea, scale, sourceUnfolding } from './geom.js';
import { createView, drawSolid, faceColor, pick, pts, svg } from './view3d.js';
import { fmt, frame, h, row, select } from './ui.js';

export default function mount(root, cfg) {
  const ui = frame(root, {
    title: 'Source unfolding',
    help: 'Drag the solid to rotate it. Click a face, or drag the source point, to move the source. Move the pointer over the net to see a radial segment and the path it folds to. Computed in JavaScript as an illustration; not checked by Lean.',
  });
  let kind = SOLIDS[cfg.solid] ? cfg.solid : 'cube';
  let mesh, source, U, edge, hover = null;
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

  const view = createView({
    draw: drawSpace,
    onPress: (ev) => ev.target.classList?.contains('v3-source'),
    onDrag: (at) => { const p = pick(view, mesh, at); if (p) setSource(p); },
    onClick: (at) => { const p = pick(view, mesh, at); if (p) setSource(p); },
  });
  ui.stage.append(h('div', { class: 'viz-pair' }, view.el, net));
  ui.controls.append(select(Object.entries(SOLIDS).map(([k, s]) => [k, s.label]), kind, (k) => { kind = k; reset(); }));

  function reset() {
    mesh = SOLIDS[kind].make();
    // Start on the face that looks most directly at the viewer.
    let face = 0;
    mesh.frames.forEach((fr, f) => { if (view.project(fr.n)[2] > view.project(mesh.frames[face].n)[2]) face = f; });
    setSource({ face, bary: [0.5, 0.2, 0.3] });
  }
  function setSource(p) {
    source = { face: p.face, bary: clampBary(p.bary) };
    U = sourceUnfolding(mesh, source.face, sourcePoint());
    edge = frontier(U.fragments);
    hover = null;
    drawNet();
    drawSpace();
    drawState();
  }

  function drawSpace() {
    const { back, front } = drawSolid(view, mesh);
    const cutBack = svg('g'), cutFront = svg('g');
    for (const e of edge) {
      const a = view.project(fold(mesh, e.fragment, e.a)), b = view.project(fold(mesh, e.fragment, e.b));
      const isFront = view.facing(mesh.frames[e.fragment.piece.face].n);
      (isFront ? cutFront : cutBack).append(svg('line', { x1: a[0], y1: a[1], x2: b[0], y2: b[1], class: `cut${isFront ? '' : ' hidden'}` }));
    }
    const s = view.project(mesh.place(source.face, sourcePoint()));
    const sFront = view.facing(mesh.frames[source.face].n);
    const marker = svg('circle', { cx: s[0], cy: s[1], r: 6, class: `v3-source${sFront ? '' : ' hidden'}` });
    const path = svg('g');
    if (hover) {
      const p = foldedPath(mesh, hover.fragment, hover.z).map(view.project);
      path.append(svg('polyline', { points: pts(p), class: 'geodesic' }));
      const end = p[p.length - 1];
      path.append(svg('circle', { cx: end[0], cy: end[1], r: 3.5, class: 'geodesic-end' }));
    }
    view.el.replaceChildren(back, cutBack, front, cutFront, path, marker);
  }

  let k = 1;
  function drawNet() {
    const reach = Math.max(...U.fragments.flatMap((f) => f.poly.pts.map(norm)));
    k = (W / 2 - 10) / reach;
    const at = (p) => [p[0] * k, -p[1] * k];
    const fill = svg('g'), seams = svg('g'), cut = svg('g');
    for (const { piece, poly } of U.fragments) {
      const colour = faceColor(mesh.groups[piece.face]);
      fill.append(svg('polygon', { points: pts(poly.pts.map(at)), fill: colour, 'fill-opacity': 0.5, stroke: colour, 'stroke-opacity': 0.5, 'stroke-width': 0.6 }));
      poly.pts.forEach((p, i) => {
        if (poly.tags[i] !== 'seam') return;
        const a = at(p), b = at(poly.pts[(i + 1) % poly.pts.length]);
        seams.append(svg('line', { x1: a[0], y1: a[1], x2: b[0], y2: b[1], class: 'net-seam' }));
      });
    }
    for (const e of edge) {
      const a = at(e.a), b = at(e.b);
      cut.append(svg('line', { x1: a[0], y1: a[1], x2: b[0], y2: b[1], class: 'cut' }));
    }
    const radial = svg('g', { class: 'radial' });
    net.replaceChildren(fill, seams, cut, radial, svg('circle', { cx: 0, cy: 0, r: 5, class: 'v3-source still' }));
    net.radial = radial;
  }
  const netPoint = (ev) => {
    const box = net.getBoundingClientRect();
    return [((ev.clientX - box.left) * W / box.width - W / 2) / k, -((ev.clientY - box.top) * W / box.height - W / 2) / k];
  };
  net.addEventListener('pointermove', (ev) => {
    const z = netPoint(ev);
    const fragment = locate(U.fragments, z);
    hover = fragment ? { fragment, z } : null;
    net.radial.replaceChildren();
    if (hover) {
      net.radial.append(svg('line', { x1: 0, y1: 0, x2: z[0] * k, y2: -z[1] * k, class: 'geodesic' }),
        svg('circle', { cx: z[0] * k, cy: -z[1] * k, r: 3.5, class: 'geodesic-end' }));
    }
    drawSpace();
    drawState();
  });
  net.addEventListener('pointerleave', () => { hover = null; net.radial.replaceChildren(); drawSpace(); drawState(); });

  function drawState() {
    const area = U.fragments.reduce((s, f) => s + polygonArea(f.poly.pts), 0);
    ui.state.replaceChildren(
      row('area of the net', `${fmt(area, 4)} &nbsp;(surface: ${fmt(mesh.area(), 4)})`),
      row('pieces', `${new Set(U.fragments.map((f) => f.piece)).size} polygons, each folded by one rigid motion`),
      hover
        ? row('‖z‖ = distance on the surface', `${fmt(norm(hover.z), 4)} &nbsp;(straight through the solid: ${fmt(dist(fold(mesh, hover.fragment, hover.z), mesh.place(source.face, sourcePoint())), 4)})`)
        : row('‖z‖ = distance on the surface', '<em>point at the net</em>'),
    );
  }
  reset();
}
