module

public import Unfoldings.Cone.AngularInjective
public import Unfoldings.Metric.Polygonal

/-! A whole sector chart retaining physical coordinates retains its original center. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AngularFan

variable {n : ℕ} (F : AngularFan n) {region : Set ℂ}

/-- A physical corner chart is centered because the genuine angular model has injective
physical coordinates. This applies to convex, half-plane and reentrant sector models. -/
theorem physical_chart_center (small : F.totalAngle < 2 * Real.pi)
    (x : PolygonalPoint region) {r : ℝ} (positive : 0 < r) (frame : ℂ ≃ₗᵢ[ℝ] ℂ)
    (A : Metric.eball x (ENNReal.ofReal r) ≃ᵢ Metric.eball F.origin (ENNReal.ofReal r))
    (physical : ∀ y, x.val + frame (F.develop (A y).val) = y.val.val) :
    (A ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩).val = F.origin := by
  let root : Metric.eball x (ENNReal.ofReal r) :=
    ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩
  have placed := physical root
  have zero : frame (F.develop (A root).val) = 0 :=
    add_left_cancel (placed.trans (add_zero x.val).symm)
  apply F.develop_injective_of_lt_full small
  rw [F.develop_origin]
  exact frame.injective (zero.trans (map_zero frame).symm)

end Unfoldings.AngularFan
