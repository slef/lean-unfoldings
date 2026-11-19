module

public import Unfoldings.Metric.BankHalfPlaneChart

/-! Reflections of the real and imaginary axes normalize bank time and the occupied side. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

/-- Reflect real displacement and the occupied side independently. -/
def bankAxisFrame : Bool → Bool → ℂ ≃ₗᵢ[ℝ] ℂ
  | false, false => LinearIsometryEquiv.refl ℝ ℂ
  | false, true => Complex.conjLIE
  | true, false => Complex.conjLIE.trans (LinearIsometryEquiv.neg ℝ)
  | true, true => LinearIsometryEquiv.neg ℝ

theorem bankAxisFrame_im (reverse flip : Bool) (z : ℂ) :
    (bankAxisFrame reverse flip z).im = if flip then -z.im else z.im := by
  cases reverse <;> cases flip <;> simp [bankAxisFrame]

theorem bankAxisFrame_ofReal (reverse flip : Bool) (x : ℝ) :
    bankAxisFrame reverse flip (x : ℂ) = ((if reverse then -x else x : ℝ) : ℂ) := by
  cases reverse <;> cases flip <;> simp [bankAxisFrame]

/-- Restrict a rigid map to sets related by its exact membership criterion. -/
def setIsometryEquiv {X Y : Type*} [EMetricSpace X] [EMetricSpace Y]
    (A : X ≃ᵢ Y) (S : Set X) (T : Set Y) (membership : ∀ x, A x ∈ T ↔ x ∈ S) :
    S ≃ᵢ T where
  toFun x := ⟨A x.val, (membership _).mpr x.property⟩
  invFun y := ⟨A.symm y.val, (membership _).mp ((A.apply_symm_apply y.val).symm ▸ y.property)⟩
  left_inv x := Subtype.ext (A.symm_apply_apply x.val)
  right_inv y := Subtype.ext (A.apply_symm_apply y.val)
  isometry_toFun x y := A.isometry x.val y.val

@[simp] theorem setIsometryEquiv_val {X Y : Type*} [EMetricSpace X] [EMetricSpace Y]
    (A : X ≃ᵢ Y) {S : Set X} {T : Set Y} (membership : ∀ x, A x ∈ T ↔ x ∈ S)
    (x : S) : (setIsometryEquiv A S T membership x).val = A x.val := rfl

/-- The standard upper half-plane can be normalized to either side with either axis direction. -/
def bankUpperNormalize (reverse side : Bool) : bankHalfPlane false ≃ᵢ bankHalfPlane side :=
  setIsometryEquiv (bankAxisFrame reverse side).toIsometryEquiv _ _ (by
    intro z
    change (if side then (bankAxisFrame reverse side z).im ≤ 0
      else 0 ≤ (bankAxisFrame reverse side z).im) ↔ 0 ≤ z.im
    rw [bankAxisFrame_im]
    cases side <;> simp)

end Unfoldings.MetricGluing
