module

public import Unfoldings.Metric.BallIsometry

/-! Unique lifts through whole-ball metric charts preserve continuity. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings

variable {A X Y : Type*} [TopologicalSpace A] [EMetricSpace X] [EMetricSpace Y]

/-- Whole-ball isometries and unique fibers make a lift continuous on any parameter space. -/
theorem continuous_lift_of_ball_charts (f : A → X) (g : A → Y) (F : X → Y)
    (continuous : Continuous g) (unique : ∀ t x, F x = g t → x = f t)
    (charts : ∀ t, ∃ r : ℝ, 0 < r ∧
      ∃ B : Metric.eball (f t) (ENNReal.ofReal r) ≃ᵢ
        Metric.eball (g t) (ENNReal.ofReal r), ∀ z, (B z).val = F z.val) :
    Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨r, positive, B, agrees⟩ := charts t
  let U := g ⁻¹' Metric.eball (g t) (ENNReal.ofReal r)
  have open_U : IsOpen U := Metric.isOpen_eball.preimage continuous
  have at_t : t ∈ U := Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)
  have inverse (u : U) : (B.symm ⟨g u.val, u.property⟩).val = f u.val := by
    apply unique
    exact (agrees (B.symm ⟨g u.val, u.property⟩)).symm.trans
      (congrArg Subtype.val (B.apply_symm_apply ⟨g u.val, u.property⟩))
  have local_continuous : Continuous (fun u : U => f u.val) := by
    have lift_continuous : Continuous (fun u : U =>
        (⟨g u.val, u.property⟩ : Metric.eball (g t) (ENNReal.ofReal r))) :=
      (continuous.comp continuous_subtype_val).subtype_mk _
    have composed := continuous_subtype_val.comp (B.symm.continuous.comp lift_continuous)
    exact composed.congr inverse
  have continuous_on : ContinuousOn f U :=
    continuousOn_iff_continuous_domRestrict.mpr local_continuous
  exact continuous_on.continuousAt (open_U.mem_nhds at_t)

end Unfoldings
