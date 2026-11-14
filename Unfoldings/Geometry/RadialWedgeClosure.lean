module

public import Unfoldings.Geometry.RadialClosureJordan
public import Unfoldings.Geometry.WedgeClosingDirection

/-! Construct radial-wedge Jordan closures from the actual path geometry. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n) (source : Plane)

/-- A pointed wedge admits the three-segment Jordan closure used in turn comparison. -/
theorem exists_radial_wedge_closure (radial : P.RadialFrom source 0)
    (initial : 0 < dist source (P.vertex 0))
    (progress : dist source (P.vertex 0) < dist source (P.vertex (Fin.last n)))
    (frame : (ℝ × ℝ) ≃ₗ[ℝ] Plane)
    (inside : ∀ z ∈ Set.range P.path,
      0 ≤ (frame.symm (z - source)).1 ∧ 0 ≤ (frame.symm (z - source)).2) :
    ∃ c : Plane,
      ((frame.symm (c - source)).1 < 0 ∨ (frame.symm (c - source)).2 < 0) ∧
      0 < inner ℝ (P.vertex (Fin.last n) - source) (c - P.vertex (Fin.last n)) ∧
      Schoenflies.IsJordanCurve (Set.range P.path ∪
        ((segment ℝ (P.vertex (Fin.last n)) c ∪ segment ℝ c source) ∪
          segment ℝ source (P.vertex 0))) := by
  have endpoint : P.vertex (Fin.last n) ∈ Set.range P.path := ⟨1, P.path.target⟩
  have nonzero : P.vertex (Fin.last n) - source ≠ 0 := by
    intro zero
    have same := sub_eq_zero.mp zero
    rw [same, dist_self] at progress
    linarith
  obtain ⟨height, supporting, direction, negative, outward_direction⟩ :=
    exists_wedge_closing_direction frame (P.vertex (Fin.last n) - source) nonzero
      (inside _ endpoint)
  obtain ⟨t, positive, outward⟩ :=
    exists_outward_closing_point source (P.vertex (Fin.last n)) direction outward_direction
  let c := source + t • direction
  have outside : height (c - source) < 0 := by
    simpa only [c, add_sub_cancel_left, map_smul, smul_eq_mul] using
      mul_neg_of_pos_of_neg positive negative
  have excluded : (frame.symm (c - source)).1 < 0 ∨ (frame.symm (c - source)).2 < 0 := by
    by_cases first : (frame.symm (c - source)).1 < 0
    · exact Or.inl first
    · right
      by_contra second
      exact not_le_of_gt outside
        (supporting (c - source) (le_of_not_gt first) (le_of_not_gt second))
  refine ⟨c, excluded, outward, ?_⟩
  exact P.radial_halfplane_closure_jordan source radial initial progress height
    (fun z hz => supporting (z - source) (inside z hz).1 (inside z hz).2) c outside outward

end Unfoldings.PolygonalChain
