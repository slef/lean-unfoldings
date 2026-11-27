// The geometry behind the figures, checked against facts that the Lean
// definitions imply. Nothing here is a proof; it guards the illustrations.

import test from 'node:test';
import assert from 'node:assert/strict';
import * as G from '../src/assets/viz/geom.js';

const close = (a, b, eps = 1e-7) => assert.ok(Math.abs(a - b) < eps, `${a} ≠ ${b}`);
const sources = [[0, [1 / 3, 1 / 3, 1 / 3]], [1, [0.2, 0.5, 0.3]], [2, [0.05, 0.9, 0.05]], [3, [0.6, 0.1, 0.3]]];
const pointOf = (mesh, f, w) => [0, 1].map((k) => w[0] * mesh.vertex[f][0][k] + w[1] * mesh.vertex[f][1][k] + w[2] * mesh.vertex[f][2][k]);

for (const [name, solid] of Object.entries(G.SOLIDS)) {
  const mesh = solid.make();

  test(`${name}: a closed mesh pairs every local edge exactly once`, () => {
    assert.equal(mesh.boundary.length, 0);
    assert.equal(mesh.seams.length * 2, mesh.triangles.length * 3);
    for (const { first, last } of mesh.seams) assert.notDeepEqual(first, last);
  });

  test(`${name}: identify is an isometry and agrees with the placement (joined)`, () => {
    for (const { first: [f, i] } of mesh.seams) {
      const [a, b] = mesh.edge(f, i);
      const at = (t) => G.lerp(a, b, t);
      const x = mesh.identify(f, i, 0.2), y = mesh.identify(f, i, 0.9);
      close(G.dist(at(0.2), at(0.9)), G.dist(x.point, y.point));
      close(G.dist(mesh.place(f, at(0.2)), mesh.place(x.face, x.point)), 0);
    }
  });

  test(`${name}: unfolding across an edge matches the two faces along it`, () => {
    for (const { first: [f, i] } of mesh.seams) {
      const T = mesh.unfoldAcross(f, i);
      const o = mesh.identify(f, i, 0.3);
      const [a, b] = mesh.edge(f, i);
      close(G.dist(G.apply(T, o.point), G.lerp(a, b, 0.3)), 0);
    }
  });

  for (const [f, w] of sources) {
    if (f >= mesh.triangles.length) continue;
    const U = G.sourceUnfolding(mesh, f, pointOf(mesh, f, w));
    const edge = G.frontier(U.fragments);
    test(`${name}, source in face ${f}: the net has the area of the surface`, () => {
      assert.ok(U.complete);
      close(U.fragments.reduce((s, fr) => s + G.polygonArea(fr.poly.pts), 0), mesh.area(), 1e-6);
    });
    test(`${name}, source in face ${f}: pieces are cut only along bisectors`, () => {
      for (const fr of U.fragments) for (let k = 0; k < fr.poly.pts.length; k++) assert.equal(G.taggedSegment(fr.poly, k, 'limit'), null);
    });
    test(`${name}, source in face ${f}: the net is star-shaped and its frontier is found`, () => {
      assert.ok(edge.length > 0);
      for (const e of edge) {
        const mid = G.scale(G.add(e.a, e.b), 0.5);
        assert.ok(G.locate(U.fragments, G.scale(mid, 0.999)));
        assert.equal(G.locate(U.fragments, G.scale(mid, 1.001)), null);
      }
    });
    test(`${name}, source in face ${f}: a radial segment folds to a path of the same length`, () => {
      for (const fr of U.fragments) {
        const z = G.scale(fr.poly.pts.reduce(G.add), 1 / fr.poly.pts.length);
        const path = G.foldedPath(mesh, fr, z);
        let length = 0;
        for (let k = 0; k + 1 < path.length; k++) length += G.dist(path[k], path[k + 1]);
        close(length, G.norm(z), 1e-6);
        close(G.dist(path[path.length - 1], G.fold(mesh, fr, z)), 0);
      }
    });
  }
}

test('the cap figure is a convex cap with acute faces', () => {
  for (const height of [0.02, 0.25, 0.9]) {
    const mesh = G.capMesh(height);
    const m = G.capMeasures(mesh);
    assert.ok(m.supported);
    assert.ok(m.margin > 5);
    assert.equal(mesh.boundary.length, 12);
    for (const [f, i] of mesh.boundary) close(mesh.points[mesh.triangles[f][i]][2], 0);
  }
});
