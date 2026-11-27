// A mesh as the Lean structure stores it: separate triangles, each in its own
// plane, and seams that pair whole edges. Options: { "solid": "tetrahedron" }.

import { SOLIDS, add, dist, lerp, next, scale, sub } from './geom.js';
import { createView, drawSolid, faceColor, pts, svg } from './view3d.js';
import { fmt, frame, h, mono, row } from './ui.js';

const seamColor = (s) => `hsl(${(s * 67 + 20) % 360} 70% 45%)`;

export default function mount(root, cfg) {
  const ui = frame(root, {
    title: 'A mesh and its seams',
    help: 'Right: the faces as the mesh stores them, each in its own plane. Two edges of the same colour are paired by a seam. Move the pointer along an edge to see the point that `identify` pairs with it, and where both lie on the solid. Edges drawn dashed on the solid are flat: the two faces are coplanar.',
  });
  const kind = SOLIDS[cfg.solid] ? cfg.solid : 'tetrahedron';
  const mesh = SOLIDS[kind].make();
  const F = mesh.triangles.length;
  const cols = F <= 4 ? 2 : F <= 9 ? 3 : 4, rows = Math.ceil(F / cols);
  const cell = F <= 4 ? 170 : F <= 9 ? 130 : 105;
  const flat = svg('svg', { viewBox: `0 0 ${cols * cell} ${rows * cell}`, width: cols * cell, height: rows * cell, class: 'meshview', role: 'img' });
  let hover = null;

  // Each face is drawn in its own cell, scaled by a common factor.
  const size = Math.max(...mesh.vertex.flatMap((v) => [0, 1, 2].map((i) => dist(v[i], v[next(i)]))));
  const k = (cell - 34) / size;
  const centre = (f) => scale(mesh.vertex[f].reduce(add), 1 / 3);
  const at = (f, p) => {
    const c = centre(f);
    return [(f % cols + 0.5) * cell + (p[0] - c[0]) * k, (Math.floor(f / cols) + 0.5) * cell - (p[1] - c[1]) * k];
  };

  const view = createView({ size: 260, zoom: 95, draw: drawSpace });
  ui.stage.append(h('div', { class: 'viz-pair' }, view.el, flat));

  function drawSpace() {
    const { back, front } = drawSolid(view, mesh, { highlight: hover?.face });
    const mark = svg('g');
    if (hover) {
      const p = view.project(mesh.place(hover.face, hover.point));
      mark.append(svg('circle', { cx: p[0], cy: p[1], r: 5, class: 'geodesic-end' }));
    }
    view.el.replaceChildren(back, front, mark);
  }

  function drawFlat() {
    const g = svg('g');
    for (let f = 0; f < F; f++) {
      const corners = mesh.vertex[f].map((p) => at(f, p));
      g.append(svg('polygon', { points: pts(corners), fill: faceColor(mesh.groups[f]), 'fill-opacity': hover && (hover.face === f || hover.other.face === f) ? 0.6 : 0.3, stroke: 'none' }));
      for (let i = 0; i < 3; i++) {
        const s = mesh.seamOf[f][i];
        const [a, b] = [corners[i], corners[next(i)]];
        g.append(svg('line', { x1: a[0], y1: a[1], x2: b[0], y2: b[1], stroke: s === null ? 'currentColor' : seamColor(s), 'stroke-width': hover && hover.seam === s ? 5 : 2.6, 'stroke-linecap': 'round' }));
        const c = at(f, centre(f));
        const label = lerp(corners[i], c, 0.24);
        g.append(svg('text', { x: label[0], y: label[1] + 3.5, class: 'corner-label' }, String(i)));
      }
      const c = at(f, centre(f));
      g.append(svg('text', { x: c[0], y: c[1] + 4, class: 'face-label' }, `f${f}`));
    }
    if (hover) {
      for (const side of [hover, hover.other]) {
        const p = at(side.face, side.point);
        g.append(svg('circle', { cx: p[0], cy: p[1], r: 5, class: 'geodesic-end' }));
      }
    }
    flat.replaceChildren(g);
  }

  flat.addEventListener('pointermove', (ev) => {
    const box = flat.getBoundingClientRect();
    const x = [(ev.clientX - box.left) * cols * cell / box.width, (ev.clientY - box.top) * rows * cell / box.height];
    let best = null;
    for (let f = 0; f < F; f++) {
      for (let i = 0; i < 3; i++) {
        if (mesh.seamOf[f][i] === null) continue;
        const a = at(f, mesh.vertex[f][i]), b = at(f, mesh.vertex[f][next(i)]);
        const u = sub(b, a);
        const t = Math.max(0, Math.min(1, ((x[0] - a[0]) * u[0] + (x[1] - a[1]) * u[1]) / (u[0] * u[0] + u[1] * u[1])));
        const d = dist(x, lerp(a, b, t));
        if (d < 14 && (!best || d < best.d)) best = { d, f, i, t };
      }
    }
    if (!best) hover = null;
    else {
      const [a, b] = mesh.edge(best.f, best.i);
      const o = mesh.identify(best.f, best.i, best.t);
      hover = { face: best.f, corner: best.i, t: best.t, point: lerp(a, b, best.t), seam: mesh.seamOf[best.f][best.i], other: o };
    }
    drawFlat(); drawSpace(); drawState();
  });
  flat.addEventListener('pointerleave', () => { hover = null; drawFlat(); drawSpace(); drawState(); });

  function drawState() {
    const rows2 = [row('faces, seams', `${F} triangles, ${mesh.seams.length} seams, ${3 * F} local edges (${mesh.boundary.length} unpaired)`)];
    if (hover) {
      const s = mesh.seams[hover.seam];
      rows2.push(row('seam', `${mono(`first = (f${s.first[0]}, ${s.first[1]})`)} &nbsp; ${mono(`last = (f${s.last[0]}, ${s.last[1]})`)}`));
      rows2.push(row('paired points', `on edge ${hover.corner} of f${hover.face}, ${fmt(hover.t * 100, 0)}% along &nbsp;↔&nbsp; on edge ${hover.other.corner} of f${hover.other.face}, ${fmt((1 - hover.t) * 100, 0)}% along`));
    } else rows2.push(row('seam', '<em>point at an edge</em>'));
    ui.state.replaceChildren(...rows2);
  }
  drawFlat(); drawSpace(); drawState();
}
