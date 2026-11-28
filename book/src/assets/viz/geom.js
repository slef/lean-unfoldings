// Geometry behind the figures: triangle meshes in the shape of the Lean
// `Mesh` structure, and a computation of the source unfolding.
//
// Nothing here is checked by Lean. The figures illustrate the definitions; the
// test suite (test/geom.test.mjs) checks this code against facts that the
// definitions imply, such as "the net has the area of the surface".

// --- vectors ---------------------------------------------------------------

// Written out for dimensions 2 and 3: these run in the inner loops.
export const add = (a, b) => (a.length === 2 ? [a[0] + b[0], a[1] + b[1]] : [a[0] + b[0], a[1] + b[1], a[2] + b[2]]);
export const sub = (a, b) => (a.length === 2 ? [a[0] - b[0], a[1] - b[1]] : [a[0] - b[0], a[1] - b[1], a[2] - b[2]]);
export const scale = (a, t) => (a.length === 2 ? [a[0] * t, a[1] * t] : [a[0] * t, a[1] * t, a[2] * t]);
export const dot = (a, b) => (a.length === 2 ? a[0] * b[0] + a[1] * b[1] : a[0] * b[0] + a[1] * b[1] + a[2] * b[2]);
export const norm = (a) => Math.sqrt(dot(a, a));
export const unit = (a) => scale(a, 1 / norm(a));
export const cross3 = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
export const cross2 = (a, b) => a[0] * b[1] - a[1] * b[0];
export const lerp = (a, b, t) => add(a, scale(sub(b, a), t));
export const dist = (a, b) => norm(sub(a, b));

// --- planar rigid motions ----------------------------------------------------
// [c, s, tx, ty] is the map x ↦ R x + t with R the rotation (c, -s; s, c).

export const identity = [1, 0, 0, 0];
export const apply = (T, p) => [T[0] * p[0] - T[1] * p[1] + T[2], T[1] * p[0] + T[0] * p[1] + T[3]];
export const compose = (A, B) => { // A ∘ B
  const t = apply(A, [B[2], B[3]]);
  return [A[0] * B[0] - A[1] * B[1], A[1] * B[0] + A[0] * B[1], t[0], t[1]];
};
export const inverse = (T) => {
  const c = T[0], s = -T[1];
  return [c, s, -(c * T[2] - s * T[3]), -(s * T[2] + c * T[3])];
};
/** The rigid motion that sends the segment (p, q) to the segment (a, b) of the same length. */
export function motionOnto(p, q, a, b) {
  const u = sub(q, p), v = sub(b, a);
  const n = norm(u) * norm(v);
  const c = dot(u, v) / n, s = cross2(u, v) / n;
  const t = sub(a, [c * p[0] - s * p[1], s * p[0] + c * p[1]]);
  return [c, s, t[0], t[1]];
}

// --- meshes ------------------------------------------------------------------

export const next = (i) => (i + 1) % 3;

/**
 * A mesh in the shape of the Lean structure, built from triangles in space.
 *   vertex[f][i]   corner i of face f, in the plane of that face (`Mesh.vertex`)
 *   seams[s]       { first: [f, i], last: [g, j] } (`Mesh.first`, `Mesh.last`)
 *   place(f, x)    the rigid motion of face f into space (`Polyhedron.place`)
 * A seam glues the whole edge i of f to the whole edge j of g. `identify`
 * sends a point of the first edge to the point of the last edge at the same
 * position in space.
 */
export function meshFromSpace(points, triangles, groups) {
  const F = triangles.length;
  const vertex = [], frames = [];
  for (const [a, b, c] of triangles) {
    const P0 = points[a], u = unit(sub(points[b], P0));
    const n = unit(cross3(sub(points[b], P0), sub(points[c], P0)));
    const w = cross3(n, u);
    frames.push({ origin: P0, u, w, n });
    vertex.push([a, b, c].map((v) => [dot(sub(points[v], P0), u), dot(sub(points[v], P0), w)]));
  }
  const place = (f, x) => add(frames[f].origin, add(scale(frames[f].u, x[0]), scale(frames[f].w, x[1])));
  const seams = [];
  const open = new Map();
  const seamOf = Array.from({ length: F }, () => [null, null, null]);
  for (let f = 0; f < F; f++) {
    for (let i = 0; i < 3; i++) {
      const a = triangles[f][i], b = triangles[f][next(i)];
      const key = a < b ? `${a},${b}` : `${b},${a}`;
      if (open.has(key)) {
        const first = open.get(key);
        open.delete(key);
        seamOf[first[0]][first[1]] = seams.length;
        seamOf[f][i] = seams.length;
        seams.push({ first, last: [f, i] });
      } else open.set(key, [f, i]);
    }
  }
  const mesh = { points, triangles, groups: groups ?? triangles.map((_, f) => f), vertex, frames, place, seams, seamOf };
  mesh.boundary = [...open.values()];
  mesh.edge = (f, i) => [vertex[f][i], vertex[f][next(i)]];
  /** The other side of local edge (f, i): [g, j], or null on the boundary. */
  mesh.across = (f, i) => {
    const s = seamOf[f][i];
    if (s === null) return null;
    const { first, last } = seams[s];
    return first[0] === f && first[1] === i ? last : first;
  };
  /** `identify` (or its inverse): the point at parameter t of edge (f, i) on the other side. */
  mesh.identify = (f, i, t) => {
    const [g, j] = mesh.across(f, i);
    const [a, b] = mesh.edge(g, j);
    return { face: g, corner: j, point: lerp(a, b, 1 - t) };
  };
  /** The rigid motion of the plane of g into the plane of f that unfolds g across edge (f, i). */
  mesh.unfoldAcross = (f, i) => {
    const [g, j] = mesh.across(f, i);
    const [a, b] = mesh.edge(f, i);
    const [p, q] = mesh.edge(g, j);
    return motionOnto(p, q, b, a);
  };
  mesh.area = () => vertex.reduce((s, v) => s + Math.abs(cross2(sub(v[1], v[0]), sub(v[2], v[0]))) / 2, 0);
  return mesh;
}

/** Fan-triangulate convex faces given as vertex cycles; orient them outward. */
export function solid(points, faces) {
  const centre = scale(points.reduce(add), 1 / points.length);
  const triangles = [], groups = [];
  faces.forEach((cycle, g) => {
    let c = cycle;
    const n = cross3(sub(points[c[1]], points[c[0]]), sub(points[c[2]], points[c[0]]));
    if (dot(n, sub(points[c[0]], centre)) < 0) c = [...c].reverse();
    for (let k = 1; k + 1 < c.length; k++) { triangles.push([c[0], c[k], c[k + 1]]); groups.push(g); }
  });
  return meshFromSpace(points, triangles, groups);
}

const boxPoints = (a, b, c) => [[0, 0, 0], [a, 0, 0], [a, b, 0], [0, b, 0], [0, 0, c], [a, 0, c], [a, b, c], [0, b, c]]
  .map((p) => sub(p, [a / 2, b / 2, c / 2]));
const boxFaces = [[0, 1, 2, 3], [4, 5, 6, 7], [0, 1, 5, 4], [1, 2, 6, 5], [2, 3, 7, 6], [3, 0, 4, 7]];

/**
 * The faces of the convex hull of points in convex position, as vertex cycles.
 * Used for solids given by their vertices only.
 */
export function hullFaces(points) {
  const n = points.length, faces = [], seen = new Set();
  for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) for (let c = b + 1; c < n; c++) {
    const nrm = cross3(sub(points[b], points[a]), sub(points[c], points[a]));
    if (norm(nrm) < 1e-9) continue;
    let pos = 0, neg = 0;
    const on = [];
    for (let v = 0; v < n && !(pos && neg); v++) {
      const d = dot(nrm, sub(points[v], points[a])) / norm(nrm);
      if (d > 1e-7) pos++; else if (d < -1e-7) neg++; else on.push(v);
    }
    if (pos && neg) continue;
    if (on[0] !== a || on[1] !== b) continue; // report each face once, from its two smallest vertices
    const key = on.join(',');
    if (seen.has(key)) continue;
    seen.add(key);
    const centre = scale(on.map((v) => points[v]).reduce(add), 1 / on.length);
    const u = unit(sub(points[a], centre)), w = cross3(unit(nrm), u);
    const angle = (v) => Math.atan2(dot(sub(points[v], centre), w), dot(sub(points[v], centre), u));
    faces.push([...on].sort((x, y) => angle(x) - angle(y)));
  }
  return faces;
}

const PHI = (1 + Math.sqrt(5)) / 2;
const signs = (p) => p.reduce((acc, x) => acc.flatMap((q) => (x === 0 ? [[...q, 0]] : [[...q, x], [...q, -x]])), [[]]);
const cyclic = (p) => [p, [p[1], p[2], p[0]], [p[2], p[0], p[1]]];
const hull = (points, radius) => {
  const r = Math.max(...points.map(norm));
  const pts = points.map((p) => scale(p, radius / r));
  return solid(pts, hullFaces(pts));
};
const dodecahedronPoints = () => [...signs([1, 1, 1]), ...cyclic([0, 1 / PHI, PHI]).flatMap(signs)];
const truncatedIcosahedronPoints = () => [[0, 1, 3 * PHI], [1, 2 + PHI, 2 * PHI], [PHI, 2, 2 * PHI + 1]].flatMap(cyclic).flatMap(signs);

export const SOLIDS = {
  tetrahedron: { label: 'regular tetrahedron', make: () => solid([[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]].map((p) => scale(p, 0.6)), [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]]) },
  cube: { label: 'cube', make: () => solid(boxPoints(1, 1, 1), boxFaces) },
  box: { label: 'box 1 × 1.4 × 0.7', make: () => solid(boxPoints(1, 1.4, 0.7), boxFaces) },
  octahedron: { label: 'regular octahedron', make: () => solid([[1, 0, 0], [-1, 0, 0], [0, 1, 0], [0, -1, 0], [0, 0, 1], [0, 0, -1]].map((p) => scale(p, 0.8)), [[0, 2, 4], [2, 1, 4], [1, 3, 4], [3, 0, 4], [2, 0, 5], [1, 2, 5], [3, 1, 5], [0, 3, 5]]) },
  pyramid: { label: 'square pyramid', make: () => solid([[-0.6, -0.6, -0.35], [0.6, -0.6, -0.35], [0.6, 0.6, -0.35], [-0.6, 0.6, -0.35], [0, 0, 0.65]], [[0, 1, 2, 3], [0, 1, 4], [1, 2, 4], [2, 3, 4], [3, 0, 4]]) },
  dodecahedron: { label: 'regular dodecahedron', make: () => hull(dodecahedronPoints(), 0.9) },
  truncatedIcosahedron: { label: 'truncated icosahedron', make: () => hull(truncatedIcosahedronPoints(), 0.9) },
};

// --- convex polygons ---------------------------------------------------------
// A polygon is { pts, tags }: tags[k] describes the edge from pts[k] to
// pts[k+1]. Tags: 'seam' (a triangle edge), 'ray' (a side of a visibility
// cone), 'inner' (an artefact of the convex decomposition), or
// { cut: [p, q] } for an edge on the line of the cut segment [p, q].

const EPS = 1e-9;
export const polygonArea = (pts) => {
  let a = 0;
  for (let k = 0; k < pts.length; k++) a += cross2(pts[k], pts[(k + 1) % pts.length]);
  return a / 2;
};

/** Keep the part of a convex polygon where n·x ≤ c; the new edge gets `tag`. */
export function clip(poly, n, c, tag) {
  const { pts, tags } = poly;
  const out = [], outTags = [];
  const N = pts.length;
  for (let k = 0; k < N; k++) {
    const p = pts[k], q = pts[(k + 1) % N];
    const dp = dot(n, p) - c, dq = dot(n, q) - c;
    const pin = dp <= EPS, qin = dq <= EPS;
    if (pin) { out.push(p); outTags.push(tags[k]); }
    if (pin !== qin) {
      out.push(lerp(p, q, dp / (dp - dq)));
      outTags.push(pin ? tag : tags[k]); // leaving: the new edge starts here
    }
  }
  // Drop zero-length edges.
  const pts2 = [], tags2 = [];
  for (let k = 0; k < out.length; k++) {
    if (dist(out[k], out[(k + 1) % out.length]) > 1e-10) { pts2.push(out[k]); tags2.push(outTags[k]); }
  }
  return { pts: pts2, tags: tags2 };
}

const boxOf = (pts) => {
  let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
  for (const [x, y] of pts) { if (x < x0) x0 = x; if (x > x1) x1 = x; if (y < y0) y0 = y; if (y > y1) y1 = y; }
  return [x0, y0, x1, y1];
};
const boxesMeet = (a, b) => a[0] <= b[2] + 1e-9 && b[0] <= a[2] + 1e-9 && a[1] <= b[3] + 1e-9 && b[1] <= a[3] + 1e-9;
const isEmpty = (poly) => poly.pts.length < 3 || Math.abs(polygonArea(poly.pts)) < 1e-10;
/** The inward normal form of edge k of a counterclockwise polygon: inside is n·x ≤ c. */
function edgeLine(pts, k) {
  const p = pts[k], q = pts[(k + 1) % pts.length];
  const n = [q[1] - p[1], -(q[0] - p[0])]; // outward normal
  return { n, c: dot(n, p), p, q };
}

/** Convex polygon minus convex polygon, as a list of convex polygons. */
export function subtract(A, Q, tagOf) {
  let rem = A;
  const out = [];
  for (let k = 0; k < Q.pts.length; k++) {
    const { n, c, p, q } = edgeLine(Q.pts, k);
    const outside = clip(rem, scale(n, -1), -c, tagOf(k, p, q));
    if (!isEmpty(outside)) out.push(outside);
    rem = clip(rem, n, c, 'inner');
    if (isEmpty(rem)) return out.length ? out : [A];
  }
  // `rem` is A ∩ Q. If it is negligible, A is unchanged.
  return out;
}

// --- the source unfolding ------------------------------------------------------

/** Lengths of shortest edge paths from the source to every vertex, to bound distances. */
function vertexBounds(mesh, face, s) {
  const n = mesh.points.length;
  const d = new Array(n).fill(Infinity);
  mesh.triangles[face].forEach((v, i) => { d[v] = dist(s, mesh.vertex[face][i]); });
  const done = new Array(n).fill(false);
  for (;;) {
    let best = -1;
    for (let v = 0; v < n; v++) if (!done[v] && (best < 0 || d[v] < d[best])) best = v;
    if (best < 0 || d[best] === Infinity) break;
    done[best] = true;
    for (const t of mesh.triangles) {
      if (!t.includes(best)) continue;
      for (const v of t) d[v] = Math.min(d[v], d[best] + dist(mesh.points[best], mesh.points[v]));
    }
  }
  return d;
}

const pointSegment = (a, b) => { // distance from the origin to the segment
  const u = sub(b, a);
  const t = Math.max(0, Math.min(1, -dot(a, u) / dot(u, u)));
  return norm(lerp(a, b, t));
};

/**
 * The source unfolding of a closed convex mesh from the point `s` of `face`
 * (in the coordinates of that face), which must be interior to the face.
 *
 * Step 1 enumerates the straight lines out of the source: a *piece* is a face
 * reached through a given sequence of edges, developed into the plane of the
 * source face, and cut down to the cone of directions that cross those edges
 * in order. A piece records the rigid motion `T` from its face to the plane.
 *
 * Step 2 keeps, in each piece, the points whose line is a shortest path: a
 * point is removed when another piece shows the same surface point strictly
 * closer to the origin. What remains is cut into convex *fragments*.
 */
export function sourceUnfolding(mesh, face, s, { maxPieces = 4000 } = {}) {
  const bounds = vertexBounds(mesh, face, s);
  const reach = mesh.triangles.map((t, f) => Math.min(...t.map((v, i) =>
    bounds[v] + Math.max(...mesh.vertex[f].map((w) => dist(w, mesh.vertex[f][i]))))));
  const radius = Math.max(...reach) + 1e-9;

  const pieces = [];
  const T0 = [1, 0, -s[0], -s[1]];
  const tri = (f, T) => ({ pts: mesh.vertex[f].map((v) => apply(T, v)), tags: ['seam', 'seam', 'seam'] });
  pieces.push({ face, T: T0, poly: tri(face, T0), parent: null, entry: null });

  const visit = (f, T, r, l, parent, entry) => {
    if (pieces.length >= maxPieces) return;
    // The cone between the rays r (clockwise side) and l.
    let poly = clip(tri(f, T), [r[1], -r[0]], 0, 'ray');
    poly = clip(poly, [-l[1], l[0]], 0, 'ray');
    if (isEmpty(poly)) return;
    let near = Infinity;
    for (let k = 0; k < poly.pts.length; k++) near = Math.min(near, pointSegment(poly.pts[k], poly.pts[(k + 1) % poly.pts.length]));
    if (near > radius) return;
    const piece = { face: f, T, poly, parent, entry };
    pieces.push(piece);
    for (let i = 0; i < 3; i++) {
      const a = apply(T, mesh.vertex[f][i]), b = apply(T, mesh.vertex[f][next(i)]);
      if (cross2(a, b) <= 1e-12) continue; // seen from outside: lines enter here, they do not leave
      const r2 = cross2(r, a) > 0 ? a : r;
      const l2 = cross2(b, l) > 0 ? b : l;
      if (cross2(r2, l2) <= 1e-12) continue;
      const across = mesh.across(f, i);
      if (!across) continue;
      visit(across[0], compose(T, mesh.unfoldAcross(f, i)), r2, l2, piece, [a, b]);
    }
  };
  for (let i = 0; i < 3; i++) {
    const a = apply(T0, mesh.vertex[face][i]), b = apply(T0, mesh.vertex[face][next(i)]);
    const across = mesh.across(face, i);
    if (across) visit(across[0], compose(T0, mesh.unfoldAcross(face, i)), a, b, pieces[0], [a, b]);
  }

  const byFace = new Map();
  for (const p of pieces) {
    if (!byFace.has(p.face)) byFace.set(p.face, []);
    byFace.get(p.face).push(p);
  }
  const fragments = [];
  for (const group of byFace.values()) {
    for (const p of group) {
      let parts = [p.poly];
      const box = boxOf(p.poly.pts);
      for (const q of group) {
        if (q === p || !parts.length) continue;
        const M = compose(p.T, inverse(q.T)); // the plane as q draws it → as p draws it
        const c = apply(M, [0, 0]); // where q puts the source, seen by p
        if (norm(c) < 1e-9) continue; // the same development: no competition
        // Where q shows the same surface point strictly closer: |x - c| < |x|.
        let Q = { pts: q.poly.pts.map((x) => apply(M, x)), tags: q.poly.pts.map(() => 'limit') };
        if (!boxesMeet(box, boxOf(Q.pts))) continue;
        Q = clip(Q, scale(c, -1), -dot(c, c) / 2, 'bisector');
        if (isEmpty(Q)) continue;
        const tagOf = (k, a, b) => (Q.tags[k] === 'bisector' ? { cut: [a, b] } : { limit: [a, b] });
        parts = parts.flatMap((part) => {
          let common = part;
          for (let k = 0; k < Q.pts.length && !isEmpty(common); k++) {
            const { n, c: c0 } = edgeLine(Q.pts, k);
            common = clip(common, n, c0, 'inner');
          }
          return isEmpty(common) ? [part] : subtract(part, Q, tagOf);
        });
      }
      for (const poly of parts) fragments.push({ piece: p, poly });
    }
  }
  return { pieces, fragments, radius, complete: pieces.length < maxPieces };
}

/** The part of edge k of a fragment that is a real edge of the given kind ('cut' or 'limit'). */
export function taggedSegment(poly, k, kind) {
  const tag = poly.tags[k];
  if (!tag || typeof tag !== 'object' || !tag[kind]) return null;
  const p = poly.pts[k], q = poly.pts[(k + 1) % poly.pts.length];
  const [a, b] = tag[kind];
  const u = sub(b, a), L = dot(u, u);
  const tp = dot(sub(p, a), u) / L, tq = dot(sub(q, a), u) / L;
  const lo = Math.max(0, Math.min(tp, tq)), hi = Math.min(1, Math.max(tp, tq));
  if (hi - lo < 1e-9) return null;
  return [lerp(a, b, lo), lerp(a, b, hi)];
}

/**
 * The straight segment from the origin to z, folded onto the surface: a list of
 * points in space. `fragment` is anything with the `piece` that contains z.
 */
export function foldedPath(mesh, fragment, z) {
  const chain = [];
  for (let p = fragment.piece; p; p = p.parent) chain.unshift(p);
  const pts = [mesh.place(chain[0].face, apply(inverse(chain[0].T), [0, 0]))];
  for (let k = 1; k < chain.length; k++) {
    const [a, b] = chain[k].entry;
    const u = sub(b, a);
    const t = cross2(a, u) / cross2(z, u); // the point t z lies on the line through a and b
    pts.push(mesh.place(chain[k].face, apply(inverse(chain[k].T), scale(z, t))));
  }
  const last = chain[chain.length - 1];
  pts.push(mesh.place(last.face, apply(inverse(last.T), z)));
  pts.faces = chain.map((p) => p.face); // the segment from pts[k] to pts[k + 1] lies in faces[k]
  return pts;
}

export const fold = (mesh, fragment, z) => mesh.place(fragment.piece.face, apply(inverse(fragment.piece.T), z));

/**
 * The frontier of the union of the fragments: the parts of fragment edges
 * that no other fragment continues across. Returns [{ fragment, a, b }].
 * By the theorem these fold onto the cut locus.
 */
export function frontier(fragments) {
  const edges = [];
  fragments.forEach((fragment, index) => {
    const { pts } = fragment.poly;
    for (let k = 0; k < pts.length; k++) edges.push({ index, fragment, a: pts[k], b: pts[(k + 1) % pts.length] });
  });
  const out = [];
  for (const e of edges) {
    const u = sub(e.b, e.a), L = norm(u);
    if (L < 1e-9) continue;
    const d = scale(u, 1 / L);
    let free = [[0, L]];
    const [dx, dy] = d, [ax, ay] = e.a;
    for (const o of edges) {
      if (o.index === e.index) continue;
      if (Math.abs(dx * (o.a[1] - ay) - dy * (o.a[0] - ax)) > 1e-7 || Math.abs(dx * (o.b[1] - ay) - dy * (o.b[0] - ax)) > 1e-7) continue;
      if (dot(d, sub(o.b, o.a)) > 0) continue; // a neighbour runs the other way
      const lo = dot(d, sub(o.b, e.a)), hi = dot(d, sub(o.a, e.a));
      free = free.flatMap(([x, y]) => [[x, Math.min(y, lo)], [Math.max(x, hi), y]].filter(([p, q]) => q - p > 1e-7));
      if (!free.length) break;
    }
    for (const [x, y] of free) out.push({ fragment: e.fragment, a: add(e.a, scale(d, x)), b: add(e.a, scale(d, y)) });
  }
  return out;
}

/** The fragment containing the point z of the plane, if any. `key` names the polygon to test. */
export function locate(fragments, z, key = 'poly') {
  return fragments.find(({ [key]: poly }) => poly.pts.every((p, k) => cross2(sub(poly.pts[(k + 1) % poly.pts.length], p), sub(z, p)) >= -1e-9)) ?? null;
}

// --- the star unfolding ----------------------------------------------------------

/**
 * The star unfolding from the same source, computed from the source unfolding U.
 *
 * The surface is cut along a shortest path from the source to every vertex.
 * In the source unfolding these paths are the segments from the origin to the
 * images of the vertices, and they divide the net into *wedges*, one between
 * each pair of consecutive vertices. The star unfolding consists of the same
 * wedges, glued back along the cut locus instead of along the radial cuts.
 *
 * Returns
 *   images   [{ vertex, z }] the vertices as the source unfolding shows them, by angle
 *   wedges   [{ M, apex }] the rigid motion of wedge i (between images i and i+1)
 *            from the source unfolding to the star unfolding, and the image of the source
 *   parts    [{ piece, poly, wedge, flat }] convex pieces: `poly` in the source
 *            unfolding, `flat` in the star unfolding
 *   outline  the polygon of the star unfolding: source image, vertex, source image, …
 *   ridge    [[a, b]] the cut locus, drawn in the star unfolding
 * When a vertex is reached by several shortest paths, one of them is cut.
 * `edge` is `frontier(U.fragments)`, if the caller has it already.
 */
export function starUnfolding(mesh, U, edge) {
  const images = [];
  mesh.points.forEach((P, vertex) => {
    let best = null;
    for (const fr of U.fragments) {
      if (!mesh.triangles[fr.piece.face].includes(vertex)) continue;
      for (const z of fr.poly.pts) {
        if (dist(fold(mesh, fr, z), P) < 1e-6 && (!best || norm(z) < norm(best.z) - 1e-9)) best = { vertex, z, fragment: fr };
      }
    }
    if (best) images.push(best);
  });
  const angle = (z) => Math.atan2(z[1], z[0]);
  images.sort((a, b) => angle(a.z) - angle(b.z));
  const n = images.length;

  // Split the fragments along the radial cuts.
  const parts = [];
  const leftOf = (r) => [r[1], -r[0]], rightOf = (l) => [-l[1], l[0]];
  for (let i = 0; i < n; i++) {
    const a = images[i].z, b = images[(i + 1) % n].z;
    const span = (angle(b) - angle(a) + 2 * Math.PI) % (2 * Math.PI) || 2 * Math.PI;
    let cones = [[a, 'radial', b, 'radial']];
    if (span > Math.PI - 1e-9) { // not convex: halve it
      const t = angle(a) + span / 2, m = [Math.cos(t), Math.sin(t)];
      cones = [[a, 'radial', m, 'inner'], [m, 'inner', b, 'radial']];
    }
    for (const [r, rTag, l, lTag] of cones) {
      for (const fr of U.fragments) {
        const pts = fr.poly.pts;
        if (pts.every((z) => cross2(r, z) < 1e-9) || pts.every((z) => cross2(z, l) < 1e-9)) continue;
        let poly = clip(fr.poly, leftOf(r), 0, rTag);
        if (!isEmpty(poly)) poly = clip(poly, rightOf(l), 0, lTag);
        if (!isEmpty(poly)) parts.push({ piece: fr.piece, poly, wedge: i });
      }
    }
  }

  // Glue the wedges along the cut locus: match the two sides of each ridge in space.
  // A radial cut meets the frontier of the net only at a vertex, which is a
  // corner of it, so each frontier segment lies in one wedge.
  const wedgeOf = (z) => {
    const t = angle(z);
    let i = n - 1;
    for (let k = 0; k < n; k++) if (angle(images[k].z) <= t) i = k;
    return i;
  };
  const sides = (edge ?? frontier(U.fragments)).map((e) => ({
    wedge: wedgeOf(lerp(e.a, e.b, 0.5)), a: e.a, b: e.b, A: fold(mesh, e.fragment, e.a), B: fold(mesh, e.fragment, e.b),
  }));
  for (const e of sides) { e.mid = lerp(e.A, e.B, 0.5); e.half = dist(e.A, e.B) / 2; }
  const far = (e, o) => {
    const x = e.mid[0] - o.mid[0], y = e.mid[1] - o.mid[1], z = e.mid[2] - o.mid[2], r = e.half + o.half;
    return x * x + y * y + z * z > r * r;
  };
  const links = Array.from({ length: n }, () => []);
  for (const e of sides) {
    const L = dist(e.A, e.B), d = scale(sub(e.B, e.A), 1 / L);
    const off = (P) => norm(sub(sub(P, e.A), scale(d, dot(sub(P, e.A), d))));
    for (const o of sides) {
      if (o.wedge === e.wedge || far(e, o) || off(o.A) > 1e-6 || off(o.B) > 1e-6) continue;
      const ta = dot(sub(o.A, e.A), d), tb = dot(sub(o.B, e.A), d);
      const lo = Math.max(0, Math.min(ta, tb)), hi = Math.min(L, Math.max(ta, tb));
      if (hi - lo < 1e-6) continue;
      const onE = (t) => lerp(e.a, e.b, t / L);
      const onO = (t) => lerp(o.a, o.b, (t - ta) / (tb - ta));
      // The motion that lays o's side of the ridge onto e's side.
      links[e.wedge].push({ to: o.wedge, R: motionOnto(onO(lo), onO(hi), onE(lo), onE(hi)), length: hi - lo });
    }
  }
  const wedges = Array.from({ length: n }, () => null);
  if (n) wedges[0] = { M: identity };
  for (let queue = [0]; queue.length;) {
    const w = queue.shift();
    // Longest ridges first: they give the most accurate motions.
    for (const { to, R } of links[w].sort((x, y) => y.length - x.length)) {
      if (wedges[to]) continue;
      wedges[to] = { M: compose(wedges[w].M, R) };
      queue.push(to);
    }
  }
  const complete = U.complete && n === mesh.points.length && wedges.every(Boolean);
  if (!complete) return { complete, images, wedges: [], parts: [], outline: [], ridge: [] };
  for (const w of wedges) w.apex = apply(w.M, [0, 0]);
  for (const part of parts) part.flat = { pts: part.poly.pts.map((z) => apply(wedges[part.wedge].M, z)), tags: part.poly.tags };
  const outline = wedges.flatMap((w, i) => [w.apex, apply(w.M, images[(i + 1) % n].z)]);
  const ridge = sides.map((e) => [e.a, e.b].map((z) => apply(wedges[e.wedge].M, z)));
  return { complete, images, wedges, parts, outline, ridge };
}

// --- a convex cap ----------------------------------------------------------------

/**
 * A cap over a regular 12-gon: 19 vertices lifted to the paraboloid
 * z = height · (1 - x² - y²), so the rim lies in the plane z = 0.
 * Returns a mesh with 24 faces and 12 boundary edges.
 */
export function capMesh(height, inner = 0.55) {
  const polar = (r, deg) => [r * Math.cos(deg * Math.PI / 180), r * Math.sin(deg * Math.PI / 180)];
  const flat = [[0, 0]];
  for (let i = 0; i < 6; i++) flat.push(polar(inner, 60 * i)); // 1..6
  for (let k = 0; k < 12; k++) flat.push(polar(1, 30 * k)); // 7..18
  const points = flat.map(([x, y]) => [x, y, height * (1 - x * x - y * y)]);
  const inn = (i) => 1 + (i % 6), out = (k) => 7 + (k % 12);
  const triangles = [];
  for (let i = 0; i < 6; i++) {
    triangles.push([0, inn(i), inn(i + 1)]);
    triangles.push([inn(i), out(2 * i + 1), inn(i + 1)]);
    triangles.push([inn(i), out(2 * i), out(2 * i + 1)]);
    triangles.push([inn(i + 1), out(2 * i + 1), out(2 * i + 2)]);
  }
  return meshFromSpace(points, triangles);
}

/** The quantities the cap theorem speaks about, in degrees. */
export function capMeasures(mesh) {
  const deg = 180 / Math.PI;
  let tilt = 0, margin = Infinity, supported = true;
  mesh.triangles.forEach((t, f) => {
    const { n, origin } = mesh.frames[f];
    tilt = Math.max(tilt, Math.acos(Math.min(1, n[2])) * deg);
    for (let i = 0; i < 3; i++) {
      const [a, b, c] = [mesh.vertex[f][i], mesh.vertex[f][next(i)], mesh.vertex[f][next(next(i))]];
      const u = sub(b, a), v = sub(c, a);
      margin = Math.min(margin, 90 - Math.acos(dot(u, v) / (norm(u) * norm(v))) * deg);
    }
    for (const p of mesh.points) if (dot(n, sub(p, origin)) > 1e-9) supported = false;
    if (n[2] <= 0) supported = false;
  });
  return { tilt, margin, supported };
}
