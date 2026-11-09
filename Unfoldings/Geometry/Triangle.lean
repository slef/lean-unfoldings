module

public import Unfoldings.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! Nondegenerate triangular cells in their own Euclidean coordinate planes. -/

@[expose] public section

namespace Unfoldings

/-- Twice the signed area, also used to test which side of a directed line contains a point. -/
def orient (a b c : Plane) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

@[simp] theorem orient_self_left (a b : Plane) : orient a b a = 0 := by simp [orient]

@[simp] theorem orient_self_right (a b : Plane) : orient a b b = 0 := by
  unfold orient
  ring

theorem orient_cyclic (a b c : Plane) : orient b c a = orient a b c := by
  unfold orient
  ring

theorem orient_swap (a b c : Plane) : orient b a c = -orient a b c := by
  unfold orient
  ring

/-- A triangular cell with genuine two-dimensional geometry. Vertex order is arbitrary. -/
structure Triangle where
  vertex : Fin 3 → Plane
  nondegenerate : orient (vertex 0) (vertex 1) (vertex 2) ≠ 0

namespace Triangle

/-- Next corner in the boundary cycle. -/
def next : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0

/-- The closed planar triangular region. -/
def carrier (T : Triangle) : Set Plane := convexHull ℝ (Set.range T.vertex)

/-- The triangle as an ordinary Euclidean metric subspace. -/
abbrev Cell (T : Triangle) : Type := T.carrier

/-- Edge `e` goes from corner `e` to its successor. -/
def edge (T : Triangle) (e : Fin 3) : Set Plane :=
  segment ℝ (T.vertex e) (T.vertex (next e))

/-- The entire closed edge, not an unspecified parameter subset. -/
abbrev Edge (T : Triangle) (e : Fin 3) : Type := T.edge e

/-- The corner not belonging to the chosen edge. -/
def opposite (T : Triangle) (e : Fin 3) : Plane := T.vertex (next (next e))

theorem vertex_mem (T : Triangle) (i : Fin 3) : T.vertex i ∈ T.carrier :=
  subset_convexHull ℝ _ ⟨i, rfl⟩

theorem convex_carrier (T : Triangle) : Convex ℝ T.carrier := convex_convexHull ℝ _

theorem compact_carrier (T : Triangle) : IsCompact T.carrier :=
  (Set.finite_range T.vertex).isCompact_convexHull ℝ

/-- The signed-area condition gives the full affine plane, not a degenerate segment. -/
theorem affineSpan_vertices (T : Triangle) : affineSpan ℝ (Set.range T.vertex) = ⊤ := by
  apply top_unique
  intro x _
  let a := T.vertex 0
  let u := T.vertex 1 - a
  let v := T.vertex 2 - a
  let determinant := u 0 * v 1 - u 1 * v 0
  have determinant_ne : determinant ≠ 0 := T.nondegenerate
  let r := ((x 0 - a 0) * v 1 - (x 1 - a 1) * v 0) / determinant
  let s := (u 0 * (x 1 - a 1) - u 1 * (x 0 - a 0)) / determinant
  have expression : r • u + s • v + a = x := by
    ext i
    fin_cases i
    · change r * u 0 + s * v 0 + a 0 = x 0
      dsimp [r, s]
      field_simp
      dsimp [determinant]
      ring
    · change r * u 1 + s * v 1 + a 1 = x 1
      dsimp [r, s]
      field_simp
      dsimp [determinant]
      ring
  let span := affineSpan ℝ (Set.range T.vertex)
  have ha : a ∈ span := subset_affineSpan ℝ _ ⟨0, rfl⟩
  have hu : u ∈ span.direction := AffineSubspace.vsub_mem_direction
    (subset_affineSpan ℝ _ ⟨1, rfl⟩) ha
  have hv : v ∈ span.direction := AffineSubspace.vsub_mem_direction
    (subset_affineSpan ℝ _ ⟨2, rfl⟩) ha
  have combined := span.vadd_mem_of_mem_direction
    (span.direction.add_mem (span.direction.smul_mem r hu) (span.direction.smul_mem s hv)) ha
  change r • u + s • v + a ∈ span at combined
  rw [expression] at combined
  exact combined

theorem interior_nonempty (T : Triangle) : (interior T.carrier).Nonempty := by
  apply T.convex_carrier.interior_nonempty_iff_affineSpan_eq_top.mpr
  rw [carrier, affineSpan_convexHull]
  exact T.affineSpan_vertices

theorem edge_subset (T : Triangle) (e : Fin 3) : T.edge e ⊆ T.carrier :=
  T.convex_carrier.segment_subset (T.vertex_mem e) (T.vertex_mem (next e))

/-- Every numbered edge has a noncollinear opposite corner. -/
theorem orient_edge_ne_zero (T : Triangle) (e : Fin 3) :
    orient (T.vertex e) (T.vertex (next e)) (T.opposite e) ≠ 0 := by
  fin_cases e
  · exact T.nondegenerate
  · change orient (T.vertex 1) (T.vertex 2) (T.vertex 0) ≠ 0
    rw [orient_cyclic]
    exact T.nondegenerate
  · change orient (T.vertex 2) (T.vertex 0) (T.vertex 1) ≠ 0
    rw [orient_cyclic (T.vertex 1) (T.vertex 2) (T.vertex 0),
      orient_cyclic (T.vertex 0) (T.vertex 1) (T.vertex 2)]
    exact T.nondegenerate

theorem edge_endpoints_ne (T : Triangle) (e : Fin 3) :
    T.vertex e ≠ T.vertex (next e) := by
  intro equal
  apply T.orient_edge_ne_zero e
  simp [orient, equal]

/-- Include a full edge in its triangular cell. -/
def edgeMap (T : Triangle) (e : Fin 3) : T.Edge e → T.Cell :=
  fun x => ⟨x, T.edge_subset e x.property⟩

theorem edgeMap_isometry (T : Triangle) (e : Fin 3) : Isometry (T.edgeMap e) :=
  fun _ _ => rfl

end Triangle
end Unfoldings
