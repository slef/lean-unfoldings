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

    const S = G.starUnfolding(mesh, U, edge);
    const n = mesh.points.length;
    test(`${name}, source in face ${f}: the star unfolding has one wedge for each vertex`, () => {
      assert.ok(S.complete);
      assert.equal(S.wedges.length, n);
      assert.deepEqual(S.images.map((im) => im.vertex).sort((a, b) => a - b), mesh.points.map((_, v) => v));
    });
    test(`${name}, source in face ${f}: the star unfolding is a polygon with the area of the surface`, () => {
      // The two wedges at a vertex agree on where the vertex goes.
      S.wedges.forEach((w, i) => {
        const z = S.images[(i + 1) % n].z;
        close(G.dist(G.apply(w.M, z), G.apply(S.wedges[(i + 1) % n].M, z)), 0, 1e-6);
      });
      assert.equal(S.outline.length, 2 * n);
      close(Math.abs(G.polygonArea(S.outline)), mesh.area(), 1e-6);
      close(S.parts.reduce((sum, part) => sum + G.polygonArea(part.flat.pts), 0), mesh.area(), 1e-6);
    });
    test(`${name}, source in face ${f}: the star unfolding does not overlap`, () => {
      const boxes = S.parts.map((part) => [0, 1].flatMap((k) => [Math.min(...part.flat.pts.map((q) => q[k])), Math.max(...part.flat.pts.map((q) => q[k]))]));
      let overlap = 0;
      for (let i = 0; i < S.parts.length; i++) for (let j = i + 1; j < S.parts.length; j++) {
        const a = boxes[i], b = boxes[j];
        if (a[0] > b[1] || b[0] > a[1] || a[2] > b[3] || b[2] > a[3]) continue;
        let common = S.parts[i].flat;
        const Q = S.parts[j].flat.pts;
        for (let k = 0; k < Q.length && common.pts.length >= 3; k++) {
          const q0 = Q[k], q1 = Q[(k + 1) % Q.length], nrm = [q1[1] - q0[1], -(q1[0] - q0[0])];
          common = G.clip(common, nrm, G.dot(nrm, q0), 'inner');
        }
        if (common.pts.length >= 3) overlap += Math.abs(G.polygonArea(common.pts));
      }
      close(overlap, 0, 1e-6);
    });
    test(`${name}, source in face ${f}: in the star unfolding the nearest image of the source is the own one`, () => {
      for (const part of S.parts) {
        const c = G.scale(part.flat.pts.reduce(G.add), 1 / part.flat.pts.length);
        const z = G.apply(G.inverse(S.wedges[part.wedge].M), c);
        close(G.dist(c, S.wedges[part.wedge].apex), G.norm(z), 1e-9);
        for (const w of S.wedges) assert.ok(G.dist(c, w.apex) > G.norm(z) - 1e-7);
        assert.equal(G.locate(S.parts, c, 'flat'), part);
      }
    });
  }
}

test('the faces of the new solids are found from their vertices', () => {
  const count = (name) => {
    const mesh = G.SOLIDS[name].make();
    const sizes = {};
    mesh.groups.forEach((g) => { sizes[g] = (sizes[g] ?? 0) + 1; }); // a k-gon gives k - 2 triangles
    const byGon = {};
    for (const t of Object.values(sizes)) byGon[t + 2] = (byGon[t + 2] ?? 0) + 1;
    return { vertices: mesh.points.length, byGon };
  };
  assert.deepEqual(count('dodecahedron'), { vertices: 20, byGon: { 5: 12 } });
  assert.deepEqual(count('truncatedIcosahedron'), { vertices: 60, byGon: { 5: 12, 6: 20 } });
});

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
