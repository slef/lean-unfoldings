module

public import Unfoldings.Metric.BallChart

/-! Whole-ball metric regularity is invariant under intrinsic isometries. -/

@[expose] public section

open scoped ENNReal

namespace Unfoldings

variable {X Y E : Type*} [EMetricSpace X] [EMetricSpace Y] [PseudoMetricSpace E]

/-- Restrict a global intrinsic isometry to corresponding whole open balls. -/
def isometryEquivEBall (A : X ≃ᵢ Y) (x : X) (r : ℝ≥0∞) :
    Metric.eball x r ≃ᵢ Metric.eball (A x) r where
  toEquiv :=
    { toFun y := ⟨A y.val, by simpa only [Metric.mem_eball, A.isometry.edist_eq] using y.property⟩
      invFun y := ⟨A.symm y.val, by
        have bound := y.property
        change edist y.val (A x) < r at bound
        change edist (A.symm y.val) x < r
        rw [← A.isometry.edist_eq, A.apply_symm_apply]
        exact bound⟩
      left_inv y := Subtype.ext (A.symm_apply_apply y.val)
      right_inv y := Subtype.ext (A.apply_symm_apply y.val) }
  isometry_toFun x y := A.isometry x.val y.val

theorem HasMetricBallChart.isometryEquiv {x : X} (regular : HasMetricBallChart E x)
    (A : X ≃ᵢ Y) : HasMetricBallChart E (A x) := by
  obtain ⟨r, positive, y, ⟨chart⟩⟩ := regular
  exact ⟨r, positive, y, ⟨(isometryEquivEBall A x (ENNReal.ofReal r)).symm.trans chart⟩⟩

theorem hasMetricBallChart_isometryEquiv_iff (A : X ≃ᵢ Y) (x : X) :
    HasMetricBallChart E (A x) ↔ HasMetricBallChart E x := by
  constructor
  · intro regular
    simpa only [A.symm_apply_apply] using regular.isometryEquiv A.symm
  · exact fun regular => regular.isometryEquiv A

end Unfoldings
