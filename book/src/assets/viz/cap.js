// A convex cap, its footprint, its tilt and its acute margin.
// Options: { "height": 0.25 }.

import { capMeasures, capMesh, next } from './geom.js';
import { createView, drawSolid, faceColor, pts, svg } from './view3d.js';
import { fmt, frame, h, label, row } from './ui.js';

export default function mount(root, cfg) {
  const ui = frame(root, {
    title: 'A convex cap',
    help: 'Left: the cap in space (drag to rotate). Right: its footprint, the horizontal projection. The slider raises the centre; the rim stays in the plane of height 0. The theorem applies when the tilt is below a bound that depends only on the acute margin.',
  });
  let height = cfg.height ?? 0.25;
  let mesh = capMesh(height);
  const W = 260;
  const top = svg('svg', { viewBox: `${-W / 2} ${-W / 2} ${W} ${W}`, width: W, height: W, class: 'capview', role: 'img' });
  const view = createView({ size: 300, zoom: 125, yaw: -0.4, pitch: 1.15, draw: drawSpace });
  ui.stage.append(h('div', { class: 'viz-pair' }, view.el, top));
  const slider = h('input', { type: 'range', class: 'vrange', min: 0.02, max: 0.9, step: 0.01, value: height, 'aria-label': 'height of the centre' });
  slider.addEventListener('input', () => { height = Number(slider.value); mesh = capMesh(height); draw(); });
  ui.controls.append(label('height of the centre', slider));

  function drawSpace() {
    const { back, front } = drawSolid(view, mesh);
    const rim = svg('g');
    for (const [f, i] of mesh.boundary) {
      const a = view.project(mesh.points[mesh.triangles[f][i]]), b = view.project(mesh.points[mesh.triangles[f][next(i)]]);
      rim.append(svg('line', { x1: a[0], y1: a[1], x2: b[0], y2: b[1], class: 'cut' }));
    }
    view.el.replaceChildren(back, front, rim);
  }
  function drawTop() {
    const k = W / 2 - 12;
    const at = (p) => [p[0] * k, -p[1] * k];
    const g = svg('g');
    mesh.triangles.forEach((t, f) => {
      g.append(svg('polygon', { points: pts(t.map((v) => at(mesh.points[v]))), fill: faceColor(mesh.groups[f]), 'fill-opacity': 0.35, class: 'v3-edge' }));
    });
    for (const [f, i] of mesh.boundary) {
      const a = at(mesh.points[mesh.triangles[f][i]]), b = at(mesh.points[mesh.triangles[f][next(i)]]);
      g.append(svg('line', { x1: a[0], y1: a[1], x2: b[0], y2: b[1], class: 'cut' }));
    }
    top.replaceChildren(g);
  }
  function draw() {
    drawSpace();
    drawTop();
    const m = capMeasures(mesh);
    ui.state.replaceChildren(
      row('tilt', `${fmt(m.tilt, 1)}°: the largest angle between a face normal and the vertical`),
      row('acute margin α', `${fmt(m.margin, 1)}°: every angle of every face is at most 90° − α`),
      row('faces, rim edges', `${mesh.triangles.length} triangles, ${mesh.boundary.length} boundary edges at height 0${m.supported ? '' : ' (not convex!)'}`),
    );
  }
  draw();
}
