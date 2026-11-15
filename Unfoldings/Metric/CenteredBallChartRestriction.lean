module

public import Unfoldings.Metric.CenteredBallRestriction

/-! Restrict centered metric-model charts while preserving every original model coordinate. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings

variable {X Y : Type*} [EMetricSpace X] [MetricSpace Y]

/-- The real and extended descriptions of a metric ball preserve every point. -/
def metricBallEBallEquiv (a : Y) (r : ℝ) :
    Metric.ball a r ≃ᵢ Metric.eball a (ENNReal.ofReal r) where
  toFun x := ⟨x.val, by rw [Metric.eball_ofReal]; exact x.property⟩
  invFun x := ⟨x.val, by rw [← Metric.eball_ofReal]; exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  isometry_toFun _ _ := rfl

/-- Restrict a centered model-ball chart to a smaller whole metric ball. -/
def restrictCenteredBallChart {x : X} {a : Y} {R r : ℝ}
    (positive : 0 < R) (small : r ≤ R)
    (B : Metric.eball x (ENNReal.ofReal R) ≃ᵢ Metric.ball a R)
    (center : (B ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩).val = a) :
    Metric.eball x (ENNReal.ofReal r) ≃ᵢ Metric.ball a r :=
  (restrictCenteredEBallEquiv (x := x) (y := a) (ENNReal.ofReal_pos.mpr positive)
    (ENNReal.ofReal_le_ofReal small) (B.trans (metricBallEBallEquiv a R)) center).trans
      (metricBallEBallEquiv a r).symm

@[simp] theorem restrictCenteredBallChart_val {x : X} {a : Y} {R r : ℝ}
    (positive : 0 < R) (small : r ≤ R)
    (B : Metric.eball x (ENNReal.ofReal R) ≃ᵢ Metric.ball a R)
    (center : (B ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩).val = a)
    (z : Metric.eball x (ENNReal.ofReal r)) :
    (restrictCenteredBallChart positive small B center z).val =
      (B ⟨z.val, z.property.trans_le (ENNReal.ofReal_le_ofReal small)⟩).val := rfl

end Unfoldings
