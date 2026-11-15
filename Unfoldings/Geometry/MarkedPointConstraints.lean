module

public import Unfoldings.Geometry.ConstraintInteriors

/-! Two actual coordinate constraints force prescribed mesh contacts to be vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- The two coordinate lines through a prescribed physical point. -/
def pointCoordinateEquation (p : Plane) (i : Fin 2) : Plane →ᵃ[ℝ] ℝ :=
  (EuclideanSpace.proj i).toLinearMap.toAffineMap - AffineMap.const ℝ Plane (p i)

@[simp] theorem pointCoordinateEquation_apply (p : Plane) (i : Fin 2) (x : Plane) :
    pointCoordinateEquation p i x = x i - p i := rfl

theorem pointCoordinateEquation_ne_zero (p : Plane) (i : Fin 2) :
    pointCoordinateEquation p i ≠ 0 := by
  intro equal
  have at_point := congrArg (fun f : Plane →ᵃ[ℝ] ℝ =>
    f (WithLp.toLp 2 (fun _ : Fin 2 => p i + 1))) equal
  change p i + 1 - p i = 0 at at_point
  linarith

namespace Triangle

/-- Independent supporting equations can meet a nondegenerate triangle only at a vertex. -/
theorem isVertex_of_two_supports (T : Triangle) (first last : Plane →ᵃ[ℝ] ℝ)
    (proper : first ≠ 0) (side_first : ∀ x ∈ T.carrier, 0 ≤ first x)
    (side_last : ∀ x ∈ T.carrier, 0 ≤ last x) {p : Plane} (member : p ∈ T.carrier)
    (zero_first : first p = 0) (zero_last : last p = 0)
    (unique : ∀ x, first x = 0 → last x = 0 → x = p) : T.IsVertex p := by
  by_contra regular
  obtain ⟨e, on_edge, whole_first⟩ := T.exists_zero_edge_of_nonvertex first proper
    side_first member regular zero_first
  have whole_last := T.affine_zero_on_edge_of_nonnegative last side_last e
    ⟨p, on_edge⟩ regular zero_last
  have initial := left_mem_segment ℝ (T.vertex e) (T.vertex (next e))
  have terminal := right_mem_segment ℝ (T.vertex e) (T.vertex (next e))
  exact T.edge_endpoints_ne e
    ((unique _ (whole_first _ initial) (whole_last _ initial)).trans
      (unique _ (whole_first _ terminal) (whole_last _ terminal)).symm)

/-- Merely prescribing signs for the coordinate lines makes their common point a mesh vertex. -/
theorem isVertex_of_coordinate_signs (T : Triangle) (p : Plane) (sign : Fin 2 → Bool)
    (side : ∀ i x, x ∈ T.carrier →
      0 ≤ AffineArrangement.signed (pointCoordinateEquation p i) (sign i) x)
    (member : p ∈ T.carrier) : T.IsVertex p := by
  let first := AffineArrangement.signed (pointCoordinateEquation p 0) (sign 0)
  let last := AffineArrangement.signed (pointCoordinateEquation p 1) (sign 1)
  apply T.isVertex_of_two_supports first last
    (AffineArrangement.signed_ne_zero _ (pointCoordinateEquation_ne_zero p 0) _)
    (side 0) (side 1) member
    ((AffineArrangement.signed_eq_zero_iff _ _ _).mpr (sub_self _))
    ((AffineArrangement.signed_eq_zero_iff _ _ _).mpr (sub_self _))
  intro x first_zero last_zero
  have left := (AffineArrangement.signed_eq_zero_iff _ _ _).mp first_zero
  have right := (AffineArrangement.signed_eq_zero_iff _ _ _).mp last_zero
  ext i
  fin_cases i
  · exact sub_eq_zero.mp left
  · exact sub_eq_zero.mp right

end Triangle
end Unfoldings
