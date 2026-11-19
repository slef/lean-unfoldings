module

public import Unfoldings.Metric.Excision
public import Unfoldings.Metric.BallIsometry

/-! Original metric-coordinate changes transport whole excision balls and their centers. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing.ForgetChart

variable {I : Type*} {E : I → Type*} [∀ i, MetricSpace (E i)]
  {R S : Total E → Total E → Prop} {inclusion : ∀ a b, R a b → S a b} {a : Total E}
  (C : ForgetChart E inclusion a)
  {X Y : Type*} [EMetricSpace X] [EMetricSpace Y]
  (A : Realization E R ≃ᵢ X) (B : Realization E S ≃ᵢ Y) (x : X) (y : Y)
  (first : A (point E R a) = x) (last : B (point E S a) = y)

/-- Express the same canonical whole-ball excision in the original source and target metrics. -/
def transportBall : Metric.eball x (ENNReal.ofReal C.radius) ≃ᵢ
    Metric.eball y (ENNReal.ofReal C.radius) :=
  ((basedEBallIsometry A (point E R a) x first (ENNReal.ofReal C.radius)).symm.trans
    C.chart).trans (basedEBallIsometry B (point E S a) y last (ENNReal.ofReal C.radius))

/-- The transported whole-ball map retains the actual original metric center. -/
theorem transportBall_center :
    (C.transportBall A B x y first last
      ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr C.positive)⟩).val = y := by
  have inverse_center : A.symm x = point E R a :=
    (congrArg A.symm first).symm.trans (A.symm_apply_apply _)
  have lifted :
      (basedEBallIsometry A (point E R a) x first (ENNReal.ofReal C.radius)).symm
        ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr C.positive)⟩ =
      ⟨point E R a, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr C.positive)⟩ :=
    Subtype.ext inverse_center
  change B ((C.chart
    ((basedEBallIsometry A (point E R a) x first (ENNReal.ofReal C.radius)).symm
      ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr C.positive)⟩)).val) = y
  rw [lifted, C.agrees, forget_point]
  exact last

end Unfoldings.MetricGluing.ForgetChart
