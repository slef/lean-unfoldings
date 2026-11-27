// A small orthographic view of a solid, drawn in SVG, rotated by dragging.

import { cross2, dot, sub } from './geom.js';

export function svg(tag, attrs = {}, ...children) {
  const e = document.createElementNS('http://www.w3.org/2000/svg', tag);
  for (const [k, v] of Object.entries(attrs)) if (v !== undefined && v !== null && v !== false) e.setAttribute(k, v);
  for (const c of children.flat()) if (c) e.append(c);
  return e;
}
export const pts = (list) => list.map((p) => `${p[0].toFixed(2)},${p[1].toFixed(2)}`).join(' ');
export const faceColor = (group) => `hsl(${(group * 137.5 + 205) % 360} 58% 60%)`;

const rotX = (a) => [[1, 0, 0], [0, Math.cos(a), -Math.sin(a)], [0, Math.sin(a), Math.cos(a)]];
const rotY = (a) => [[Math.cos(a), 0, Math.sin(a)], [0, 1, 0], [-Math.sin(a), 0, Math.cos(a)]];
const mul = (A, B) => A.map((r) => [0, 1, 2].map((j) => r[0] * B[0][j] + r[1] * B[1][j] + r[2] * B[2][j]));

/**
 * `draw(view)` is called after every rotation. Dragging rotates, unless
 * `onPress(event, [x, y])` returns true, which lets a figure claim the drag;
 * a press without movement is reported to `onClick([x, y])`.
 */
export function createView({ size = 300, zoom = 110, yaw = -0.6, pitch = 1.05, draw, onPress, onDrag, onClick }) {
  const el = svg('svg', { viewBox: `${-size / 2} ${-size / 2} ${size} ${size}`, width: size, height: size, class: 'view3d', role: 'img' });
  const view = { el, R: mul(rotX(-pitch), rotY(yaw)), zoom };
  // Screen coordinates: x right, y down; the third coordinate grows toward the viewer.
  view.project = (p) => {
    const q = view.R.map((r) => dot(r, p));
    return [q[0] * view.zoom, -q[1] * view.zoom, q[2]];
  };
  view.facing = (normal) => dot(view.R[2], normal) > 1e-9;
  view.redraw = () => draw(view);
  const local = (ev) => {
    const box = el.getBoundingClientRect();
    return [(ev.clientX - box.left) * size / box.width - size / 2, (ev.clientY - box.top) * size / box.height - size / 2];
  };
  let drag = null;
  el.addEventListener('pointerdown', (ev) => {
    const at = local(ev);
    drag = { at, start: at, moved: false, claimed: !!onPress?.(ev, at) };
    el.setPointerCapture(ev.pointerId);
    ev.preventDefault();
  });
  el.addEventListener('pointermove', (ev) => {
    if (!drag) return;
    const at = local(ev);
    if (Math.hypot(at[0] - drag.start[0], at[1] - drag.start[1]) > 4) drag.moved = true;
    if (drag.claimed) onDrag?.(at);
    else if (drag.moved) {
      view.R = mul(mul(rotX((at[1] - drag.at[1]) * 0.01), rotY((at[0] - drag.at[0]) * 0.01)), view.R);
      view.redraw();
    }
    drag.at = at;
  });
  const end = (ev) => {
    if (!drag) return;
    if (!drag.moved && !drag.claimed) onClick?.(local(ev));
    drag = null;
  };
  el.addEventListener('pointerup', end);
  el.addEventListener('pointercancel', () => { drag = null; });
  return view;
}

/** Faces of a mesh that face the viewer, front-most first, with their projected corners. */
export function visibleFaces(view, mesh) {
  return mesh.triangles.map((t, f) => ({ f, corners: t.map((v) => view.project(mesh.points[v])) }))
    .filter(({ f }) => view.facing(mesh.frames[f].n))
    .sort((a, b) => b.corners.reduce((s, c) => s + c[2], 0) - a.corners.reduce((s, c) => s + c[2], 0));
}

/** The visible face under a screen point, with barycentric coordinates there. */
export function pick(view, mesh, at) {
  for (const { f, corners } of visibleFaces(view, mesh)) {
    const [a, b, c] = corners;
    const area = cross2(sub(b, a), sub(c, a));
    const wb = cross2(sub(at, a), sub(c, a)) / area, wc = cross2(sub(b, a), sub(at, a)) / area;
    if (wb >= 0 && wc >= 0 && wb + wc <= 1) return { face: f, bary: [1 - wb - wc, wb, wc] };
  }
  return null;
}

/** Draw the solid: faces, edges (flat subdivision edges dashed), back side faint. */
export function drawSolid(view, mesh, { highlight } = {}) {
  const back = svg('g', { class: 'v3-back' }), front = svg('g', { class: 'v3-front' });
  mesh.triangles.forEach((t, f) => {
    const corners = t.map((v) => view.project(mesh.points[v]));
    const isFront = view.facing(mesh.frames[f].n);
    (isFront ? front : back).append(svg('polygon', {
      points: pts(corners), fill: faceColor(mesh.groups[f]), 'fill-opacity': isFront ? (highlight === f ? 0.75 : 0.42) : 0.1, stroke: 'none',
    }));
  });
  for (const { first, last } of mesh.seams) {
    const [f, i] = first;
    const a = view.project(mesh.points[mesh.triangles[f][i]]), b = view.project(mesh.points[mesh.triangles[f][(i + 1) % 3]]);
    const flat = mesh.groups[f] === mesh.groups[last[0]];
    const isFront = view.facing(mesh.frames[f].n) || view.facing(mesh.frames[last[0]].n);
    (isFront ? front : back).append(svg('line', {
      x1: a[0], y1: a[1], x2: b[0], y2: b[1], class: `v3-edge${flat ? ' flat' : ''}${isFront ? '' : ' hidden'}`,
    }));
  }
  return { back, front };
}
