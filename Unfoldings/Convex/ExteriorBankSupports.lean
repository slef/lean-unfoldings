module

public import Unfoldings.Convex.ExteriorActivePlanes
public import Unfoldings.Geometry.SpatialEnvelopeCutBanks
public import Unfoldings.Geometry.AffineLineSide

/-! Terminal partition cells select the one-sided supporting faces of the whole ray. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope.ExteriorPlan

variable {E : SlopeEnvelope} {V : Type*} (R : E.ExteriorPlan V) (M : E.FiniteSlopeModel)
  {A : Type} [Finite A] (P : SpatialEnvelope.WholePartition M.plane A)

theorem ray_lineMap (v : V) (t : ℝ) :
    AffineMap.lineMap (R.point v) (R.ray v 1) t = R.ray v t := by
  simp only [ray, one_smul, AffineMap.lineMap_apply_module', add_sub_cancel_left]
  exact add_comm _ _

theorem ray_endpoints_ne (v : V) : R.point v ≠ R.ray v 1 := by
  intro equal
  have offset := congrArg (fun z => z - R.point v) equal
  simp only [ray, one_smul, sub_self, add_sub_cancel_left] at offset
  have unit := R.unit v
  rw [← offset, norm_zero] at unit
  norm_num at unit

omit [Finite A] in
/-- A terminal cell's actual support is active on the entire ray, back to its original source. -/
theorem terminal_cell_support_active (v : V) (a : A) (T : ℝ)
    (tail : ∀ t : ℝ, T ≤ t → R.ray v t ∈ P.footprint a) :
    ∀ t : ℝ, 0 ≤ t → SpatialEnvelope.height M.plane (R.ray v t) =
      (M.plane (P.support a)).height (R.ray v t) := by
  let s := max T 1
  have positive : 0 < s := lt_of_lt_of_le zero_lt_one (le_max_right T 1)
  have at_s := (R.plane_active_ray_iff M v (P.support a) positive).mp
    (P.active a (R.ray v s) (tail s (le_max_left T 1)))
  intro t nonnegative
  rcases nonnegative.eq_or_lt with rfl | positive_t
  · rw [ray, zero_smul, add_zero, M.plane_active_iff]
    exact at_s.1
  · exact (R.plane_active_ray_iff M v (P.support a) positive_t).mpr at_s

omit [Finite A] in
/-- A full actual terminal cell determines the supporting face on its whole side of the ray.
Only supports active on the ray are compared here; inactive supports will be excluded locally. -/
theorem terminal_cell_support_le_on_side (v : V) (a : A) (T : ℝ)
    (tail : ∀ t : ℝ, T ≤ t → R.ray v t ∈ P.footprint a)
    (side : Bool)
    (aligned : ∀ x ∈ P.footprint a,
      0 ≤ AffineArrangement.signed (orientMap (R.point v) (R.ray v 1)) side x)
    (j : M.Face)
    (active_j : SpatialEnvelope.height M.plane (R.ray v 1) =
      (M.plane j).height (R.ray v 1)) {x : Plane}
    (on_side : 0 ≤ AffineArrangement.signed (orientMap (R.point v) (R.ray v 1)) side x) :
    (M.plane (P.support a)).height x ≤ (M.plane j).height x := by
  obtain ⟨c, interior_c⟩ := P.full a
  have member_c := interior_subset interior_c
  have signed_proper : AffineArrangement.signed (orientMap (R.point v) (R.ray v 1)) side ≠ 0 := by
    have proper := orientMap_ne_zero (R.ray_endpoints_ne v)
    cases side <;> simpa only [AffineArrangement.signed, Bool.false_eq_true, ↓reduceIte,
      neg_ne_zero] using proper
  have strict : 0 < AffineArrangement.signed (orientMap (R.point v) (R.ray v 1)) side c := by
    apply lt_of_le_of_ne (aligned c member_c)
    intro zero
    exact not_mem_interior_of_affine_lower_bound _ signed_proper aligned zero.symm interior_c
  have original_j := (R.plane_active_ray_iff M v j zero_lt_one).mp active_j
  have active_j_zero : SpatialEnvelope.height M.plane (R.point v) =
      (M.plane j).height (R.point v) :=
    (M.plane_active_iff j (R.point v)).mpr original_j.1
  have active_a_zero := R.terminal_cell_support_active M P v a T tail 0 le_rfl
  simp only [ray, zero_smul, add_zero] at active_a_zero
  have active_a_one := R.terminal_cell_support_active M P v a T tail 1 zero_le_one
  have test : 0 ≤ ((M.plane j).height - (M.plane (P.support a)).height) c := by
    have bound := AffineEnvelope.height_le (fun i => (M.plane i).height) c j
    change SpatialEnvelope.height M.plane c ≤ (M.plane j).height c at bound
    rw [P.active a c member_c] at bound
    exact sub_nonneg.mpr bound
  have bound := affine_nonnegative_on_signed_side
    ((M.plane j).height - (M.plane (P.support a)).height)
    (R.point v) (R.ray v 1) c
    (by change (M.plane j).height _ - (M.plane (P.support a)).height _ = 0
        rw [← active_j_zero, ← active_a_zero, sub_self])
    (by change (M.plane j).height _ - (M.plane (P.support a)).height _ = 0
        rw [← active_j, ← active_a_one, sub_self]) test side
    (by simpa only [AffineArrangement.signed_apply, orientMap_apply] using strict)
    (by simpa only [AffineArrangement.signed_apply, orientMap_apply] using on_side)
  exact sub_nonneg.mp bound

end Unfoldings.SlopeEnvelope.ExteriorPlan
