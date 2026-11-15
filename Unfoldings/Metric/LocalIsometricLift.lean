module

public import Unfoldings.Metric.ConvexLocalLipschitz

/-! Unique metric lifts through whole-ball isometries preserve a common Lipschitz bound. -/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace Unfoldings

variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [EMetricSpace X] [EMetricSpace Y]

/-- A lift over a convex parameter domain preserves a common Lipschitz bound when
whole-ball isometries and unique fibers are available. No global isometry is assumed. -/
theorem lipschitzWith_lift_of_ball_charts (s : Set E) (convex_s : Convex ℝ s)
    (f : s → X) (g : s → Y) (F : X → Y) (K : ℝ≥0) (bounded : LipschitzWith K g)
    (unique : ∀ u x, F x = g u → x = f u)
    (charts : ∀ u, ∃ r : ℝ, 0 < r ∧
      ∃ B : Metric.eball (f u) (ENNReal.ofReal r) ≃ᵢ
        Metric.eball (g u) (ENNReal.ofReal r), ∀ y, (B y).val = F y.val) :
    LipschitzWith K f := by
  apply convex_subtype_emetric_lipschitzWith_of_local s convex_s f K
  intro u
  obtain ⟨r, rpos, B, agrees⟩ := charts u
  have open_near : IsOpen (g ⁻¹' Metric.eball (g u) (ENNReal.ofReal r)) :=
    Metric.isOpen_eball.preimage bounded.continuous
  have inside : u ∈ g ⁻¹' Metric.eball (g u) (ENNReal.ofReal r) :=
    Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos)
  obtain ⟨ε, εpos, near⟩ := Metric.isOpen_iff.mp open_near u inside
  refine ⟨ε, εpos, ?_⟩
  intro v hv w hw
  let v' : Metric.eball (g u) (ENNReal.ofReal r) := ⟨g v, near hv⟩
  let w' : Metric.eball (g u) (ENNReal.ofReal r) := ⟨g w, near hw⟩
  have first : (B.symm v').val = f v :=
    unique v _ ((agrees (B.symm v')).symm.trans
      (congrArg (fun z : Metric.eball (g u) (ENNReal.ofReal r) => z.val)
        (B.apply_symm_apply v')))
  have last : (B.symm w').val = f w :=
    unique w _ ((agrees (B.symm w')).symm.trans
      (congrArg (fun z : Metric.eball (g u) (ENNReal.ofReal r) => z.val)
        (B.apply_symm_apply w')))
  calc
    edist (f v) (f w) = edist (B.symm v').val (B.symm w').val := by rw [first, last]
    _ = edist (g v) (g w) := B.symm.isometry.edist_eq v' w'
    _ ≤ _ := bounded.edist_le_mul v w

end Unfoldings
