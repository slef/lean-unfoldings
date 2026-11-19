module

public import Unfoldings.Cone.ReentrantSector
public import Unfoldings.Metric.BankHalfPlaneChart

/-! A half-turn fan has the ordinary Euclidean half-plane metric. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings

open MetricGluing

/-- The sector of angle pi is the standard upper half-plane, including its real axis. -/
theorem closedAngularSector_pi_eq_bankHalfPlane :
    closedAngularSector Real.pi = bankHalfPlane false := by
  ext z
  change (∃ r : ℝ≥0, ∃ θ ∈ Set.Icc 0 Real.pi, z = (r : ℂ) * polarRay θ) ↔ 0 ≤ z.im
  constructor
  · rintro ⟨r, θ, bounds, rfl⟩
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      polarRay_im]
    exact mul_nonneg r.property (Real.sin_nonneg_of_mem_Icc bounds)
  · intro above
    exact ⟨‖z‖₊, z.arg, ⟨Complex.arg_nonneg_iff.mpr above, Complex.arg_le_pi _⟩,
      (Complex.norm_mul_exp_arg_mul_I z).symm⟩

/-- The occupied upper half-plane is convex. -/
theorem convex_bankHalfPlane_upper : Convex ℝ (bankHalfPlane false) :=
  (convex_Ici (0 : ℝ)).linear_preimage Complex.imCLM.toLinearMap

/-- Keep the actual developed point of the half-turn fan as a half-plane coordinate. -/
def halfTurnFanIsometry :
    (bisectedSectorFan Real.pi Real.pi_pos (by linarith [Real.pi_pos])).Surface ≃ᵢ
      bankHalfPlane false := by
  let E := (reentrantSectorIsometryEquiv Real.pi Real.pi_pos (by linarith [Real.pi_pos])).trans
    (PolygonalPoint.congrIsometryEquiv closedAngularSector_pi_eq_bankHalfPlane)
  exact E.trans
    { toFun := PolygonalPoint.toSubtype
      invFun := PolygonalPoint.ofSubtype
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      isometry_toFun := fun x y =>
        (PolygonalPoint.edist_eq_of_segment
          (convex_bankHalfPlane_upper.segment_subset x.property y.property)).symm }

@[simp] theorem halfTurnFanIsometry_val
    (x : (bisectedSectorFan Real.pi Real.pi_pos (by linarith [Real.pi_pos])).Surface) :
    (halfTurnFanIsometry x).val =
      (bisectedSectorFan Real.pi Real.pi_pos (by linarith [Real.pi_pos])).develop x := by
  change (PolygonalPoint.congrIsometryEquiv closedAngularSector_pi_eq_bankHalfPlane
    (reentrantSectorIsometryEquiv Real.pi Real.pi_pos (by linarith [Real.pi_pos]) x)).val = _
  rw [PolygonalPoint.congrIsometryEquiv_val, reentrantSectorIsometryEquiv_val]

end Unfoldings
