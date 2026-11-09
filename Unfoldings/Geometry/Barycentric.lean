module

public import Unfoldings.Geometry.Edge
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Analysis.Convex.Combination

/-! Barycentric coordinates and local half-plane geometry at triangle edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

theorem affineIndependent_vertices (T : Triangle) : AffineIndependent ℝ T.vertex := by
  apply (affineIndependent_iff_finrank_vectorSpan_eq ℝ T.vertex (n := 2) rfl).mpr
  have span : vectorSpan ℝ (Set.range T.vertex) = ⊤ := by
    rw [← direction_affineSpan, T.affineSpan_vertices, AffineSubspace.direction_top]
  rw [span]
  simp [Plane]

/-- The genuine affine basis supplied by the three noncollinear corners. -/
def affineBasis (T : Triangle) : AffineBasis (Fin 3) ℝ Plane :=
  ⟨T.vertex, T.affineIndependent_vertices, T.affineSpan_vertices⟩

/-- Barycentric coordinates as actual affine functions on the entire plane. -/
def coord (T : Triangle) (i : Fin 3) : Plane →ᵃ[ℝ] ℝ := T.affineBasis.coord i

@[simp] theorem coord_vertex (T : Triangle) (i j : Fin 3) :
    T.coord i (T.vertex j) = if i = j then 1 else 0 := T.affineBasis.coord_apply i j

theorem continuous_coord (T : Triangle) (i : Fin 3) : Continuous (T.coord i) :=
  continuous_barycentric_coord T.affineBasis i

theorem sum_coord (T : Triangle) (x : Plane) : ∑ i, T.coord i x = 1 :=
  T.affineBasis.sum_coord_apply_eq_one x

theorem carrier_eq_nonneg_coord (T : Triangle) : T.carrier = {x | ∀ i, 0 ≤ T.coord i x} :=
  T.affineBasis.convexHull_eq_nonneg_coord

theorem interior_eq_pos_coord (T : Triangle) : interior T.carrier = {x | ∀ i, 0 < T.coord i x} :=
  T.affineBasis.interior_convexHull

theorem coord_edge_eq_zero (T : Triangle) (e : Fin 3) (x : T.Edge e) :
    T.coord (next (next e)) x = 0 := by
  have first : next (next e) ≠ e := by fin_cases e <;> decide
  have second : next (next e) ≠ next e := by fin_cases e <;> decide
  have convex : Convex ℝ {p : Plane | T.coord (next (next e)) p = 0} :=
    (convex_singleton (0 : ℝ)).affine_preimage (T.coord (next (next e)))
  exact convex.segment_subset (by simp [first]) (by simp [second]) x.property

/-- Both endpoint coordinates are positive at every nonvertex point of a closed edge. -/
theorem coord_edge_positive (T : Triangle) (e : Fin 3) (x : T.Edge e) (regular : ¬ T.IsVertex x) :
    0 < T.coord e x ∧ 0 < T.coord (next e) x := by
  have not_left : x.val ≠ T.vertex e := fun h => regular ⟨e, h.symm⟩
  have not_right : x.val ≠ T.vertex (next e) := fun h => regular ⟨next e, h.symm⟩
  have inside := mem_openSegment_of_ne_left_right not_left.symm not_right.symm x.property
  obtain ⟨t, ht, equal⟩ := (openSegment_eq_image_lineMap ℝ _ _).le inside
  have next_ne : next e ≠ e := by fin_cases e <;> decide
  have left : T.coord e x = 1 - t := by
    rw [← equal, (T.coord e).apply_lineMap]
    simp [next_ne.symm, AffineMap.lineMap_apply_ring]
  have right : T.coord (next e) x = t := by
    rw [← equal, (T.coord (next e)).apply_lineMap]
    simp [next_ne, AffineMap.lineMap_apply_ring]
  rw [left, right]
  exact ⟨sub_pos.mpr ht.2, ht.1⟩

theorem mem_carrier_iff_of_edge_coords_pos (T : Triangle) (e : Fin 3) (x : Plane)
    (left : 0 < T.coord e x) (right : 0 < T.coord (next e) x) :
    x ∈ T.carrier ↔ 0 ≤ T.coord (next (next e)) x := by
  rw [carrier_eq_nonneg_coord]
  constructor
  · intro h
    exact h _
  · intro h i
    rcases corner_cases e i with rfl | rfl | rfl
    · exact left.le
    · exact right.le
    · exact h

/-- Near a nonvertex edge point the triangle is exactly one closed affine half-plane. -/
theorem exists_ball_halfplane_edge (T : Triangle) (e : Fin 3) (x : T.Edge e)
    (regular : ¬ T.IsVertex x) : ∃ r > 0, ∀ p ∈ Metric.ball x.val r,
      (p ∈ T.carrier ↔ 0 ≤ T.coord (next (next e)) p) := by
  have open_set : IsOpen {p : Plane | 0 < T.coord e p ∧ 0 < T.coord (next e) p} :=
    (isOpen_lt continuous_const (T.continuous_coord e)).inter
      (isOpen_lt continuous_const (T.continuous_coord (next e)))
  obtain ⟨r, positive, ball⟩ := Metric.isOpen_iff.mp open_set x.val
    (T.coord_edge_positive e x regular)
  exact ⟨r, positive, fun p hp => T.mem_carrier_iff_of_edge_coords_pos e p
    (ball hp).1 (ball hp).2⟩

/-- Edge-interior points have positive distance from every other local edge. -/
theorem exists_radius_clear_other_edges (T : Triangle) (e : Fin 3) (x : T.Edge e)
    (regular : ¬ T.IsVertex x) : ∃ r > 0,
      ∀ f ≠ e, ∀ p ∈ T.edge f, r ≤ dist p x.val := by
  let others : Set Plane := ⋃ f : {f : Fin 3 // f ≠ e}, T.edge f.val
  have closed : IsClosed others :=
    isClosed_iUnion_of_finite fun f => (T.compact_edge f.val).isClosed
  have outside : x.val ∉ others := by
    intro h
    obtain ⟨f, hf⟩ := Set.mem_iUnion.mp h
    exact regular (T.isVertex_of_mem_edges f.property.symm x.property hf)
  obtain ⟨r, positive, ball⟩ := Metric.isOpen_iff.mp closed.isOpen_compl x.val outside
  refine ⟨r, positive, ?_⟩
  intro f hf p hp
  by_contra near
  have not_in := ball (Metric.mem_ball.mpr (lt_of_not_ge near))
  exact not_in (Set.mem_iUnion.mpr ⟨⟨f, hf⟩, hp⟩)

/-- A Euclidean ball intersected with the supporting half-plane of an edge. -/
def edgeHalfBall (T : Triangle) (e : Fin 3) (x : T.Edge e) (r : ℝ) : Set Plane :=
  Metric.ball x.val r ∩ {p | 0 ≤ T.coord (next (next e)) p}

/-- Local half-plane geometry identifies the half-ball with the corresponding cell ball. -/
def edgeHalfBallIsometry (T : Triangle) (e : Fin 3) (x : T.Edge e) (r : ℝ)
    (halfplane : ∀ p ∈ Metric.ball x.val r,
      (p ∈ T.carrier ↔ 0 ≤ T.coord (next (next e)) p)) :
    T.edgeHalfBall e x r ≃ᵢ Metric.ball (T.edgeMap e x) r where
  toEquiv :=
    { toFun := fun p => ⟨⟨p.val, (halfplane p.val p.property.1).mpr p.property.2⟩, by
        apply Metric.mem_ball.mpr
        exact Metric.mem_ball.mp p.property.1⟩
      invFun := fun p => ⟨p.val.val, by
        have near : p.val.val ∈ Metric.ball x.val r :=
          Metric.mem_ball.mpr (Metric.mem_ball.mp p.property)
        exact ⟨near, (halfplane p.val.val near).mp p.val.property⟩⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext (Subtype.ext rfl) }
  isometry_toFun := fun _ _ => rfl

end Unfoldings.Triangle
