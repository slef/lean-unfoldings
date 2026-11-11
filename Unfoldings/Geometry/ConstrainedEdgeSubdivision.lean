module

public import Unfoldings.Geometry.TriangleSupportingFace
public import Unfoldings.Geometry.AffineSupport
public import Unfoldings.Geometry.AffineArrangement
public import Unfoldings.Geometry.EdgePerfect

/-! Triangles respecting old supporting lines subdivide the actual whole old edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AffineArrangement

theorem signed_eq_zero_iff (height : Plane →ᵃ[ℝ] ℝ) (b : Bool) (p : Plane) :
    signed height b p = 0 ↔ height p = 0 := by
  cases b <;> simp [signed_apply]

theorem signed_ne_zero (height : Plane →ᵃ[ℝ] ℝ) (proper : height ≠ 0) (b : Bool) :
    signed height b ≠ 0 := by
  cases b <;> simpa [signed] using proper

end Unfoldings.AffineArrangement

namespace Unfoldings.Triangle

open AffineArrangement

/-- A fixed weak sign cannot change along a fine edge through a regular point. -/
theorem affine_nonnegative_on_edge_of_signed (T : Triangle) (height : Plane →ᵃ[ℝ] ℝ)
    (sign : Bool) (side : ∀ p ∈ T.carrier, 0 ≤ signed height sign p)
    (e : Fin 3) (x : T.Edge e) (regular : ¬ T.IsVertex x)
    (nonnegative : 0 ≤ height x.val) : ∀ p ∈ T.edge e, 0 ≤ height p := by
  by_cases zero : height x.val = 0
  · have signed_zero := (signed_eq_zero_iff height sign x.val).mpr zero
    have all_zero := T.affine_zero_on_edge_of_nonnegative (signed height sign) side e x
      regular signed_zero
    exact fun p member => ((signed_eq_zero_iff height sign p).mp (all_zero p member)).ge
  · have positive : 0 < height x.val := lt_of_le_of_ne nonnegative (Ne.symm zero)
    have at_x := side x.val (T.edge_subset e x.property)
    cases sign
    · have negative : height x.val ≤ 0 := by simpa [signed_apply] using at_x
      exact (not_lt_of_ge negative positive).elim
    · exact fun p member => by simpa [signed_apply] using side p (T.edge_subset e member)

/-- Each regular fine-triangle contact with an old edge belongs to a full fine edge inside it. -/
theorem exists_subedge_of_signed_coords (U T : Triangle) (signs : Fin 3 → Bool)
    (side : ∀ k p, p ∈ T.carrier → 0 ≤ signed (U.coord k) (signs k) p)
    (e : Fin 3) {x : Plane} (old_edge : x ∈ U.edge e) (inside : x ∈ T.carrier)
    (regular : ¬ T.IsVertex x) :
    ∃ f : Fin 3, x ∈ T.edge f ∧ T.edge f ⊆ U.edge e := by
  let k := next (next e)
  have old_zero : U.coord k x = 0 := U.coord_edge_eq_zero e ⟨x, old_edge⟩
  obtain ⟨f, on_edge, zero_edge⟩ := T.exists_zero_edge_of_nonvertex
    (signed (U.coord k) (signs k)) (signed_ne_zero _ (U.coord_ne_zero k) _)
    (fun p member => side k p member) inside regular
      ((signed_eq_zero_iff _ _ _).mpr old_zero)
  refine ⟨f, on_edge, fun p member => (U.mem_edge_iff e p).mpr ⟨?_, ?_⟩⟩
  · apply U.carrier_eq_nonneg_coord.ge
    intro j
    exact T.affine_nonnegative_on_edge_of_signed (U.coord j) (signs j)
      (fun p member => side j p member) f ⟨x, on_edge⟩ regular
      (U.carrier_eq_nonneg_coord.le (U.edge_subset e old_edge) j) p member
  · exact (signed_eq_zero_iff _ _ _).mp (zero_edge p member)

end Unfoldings.Triangle
