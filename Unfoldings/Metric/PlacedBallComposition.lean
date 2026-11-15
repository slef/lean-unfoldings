module

public import Unfoldings.Metric.CenteredBallChartRestriction
public import Unfoldings.Metric.BallIsometry

/-! Compose restoration and model charts while retaining their original physical placements. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings

variable {X Y Z S : Type*} [EMetricSpace X] [EMetricSpace Y] [MetricSpace Z]

/-- Compose two whole-ball charts at a common smaller radius, preserving an injective
model placement and the actual physical restoration. No model coordinates are normalized. -/
theorem exists_composed_placed_ball_chart (F : X → Y) (original : X → S) (restored : Y → S)
    (place : Z → S) (injective : Function.Injective place) {x : X} {y : Y} {a : Z}
    (image : F x = y) (restores : ∀ z, restored (F z) = original z)
    {ρ σ : ℝ} (ρpos : 0 < ρ) (σpos : 0 < σ)
    (C : Metric.eball x (ENNReal.ofReal ρ) ≃ᵢ Metric.eball (F x) (ENNReal.ofReal ρ))
    (agrees_C : ∀ z, (C z).val = F z.val)
    (H : Metric.eball y (ENNReal.ofReal σ) ≃ᵢ Metric.ball a σ)
    (agrees_H : ∀ z, place (H z).val = restored z.val)
    (model_place : place a = restored y) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ D : Metric.eball x (ENNReal.ofReal ε) ≃ᵢ Metric.ball a ε,
      ∀ z, place (D z).val = original z.val := by
  let move := basedEBallIsometry (IsometryEquiv.refl _) (F x) y image (ENNReal.ofReal ρ)
  let C' := C.trans move
  have agrees_C' (z : Metric.eball x (ENNReal.ofReal ρ)) : (C' z).val = F z.val := agrees_C z
  have center_C' : (C' ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr ρpos)⟩).val = y :=
    (agrees_C' _).trans image
  have center_H : (H ⟨y, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr σpos)⟩).val = a :=
    injective ((agrees_H _).trans model_place.symm)
  let radius := min ρ σ
  let Csmall := restrictCenteredEBallEquiv (ENNReal.ofReal_pos.mpr ρpos)
    (ENNReal.ofReal_le_ofReal (min_le_left ρ σ)) C' center_C'
  let Hsmall := restrictCenteredBallChart σpos (min_le_right ρ σ) H center_H
  have agrees_small (z : Metric.eball x (ENNReal.ofReal radius)) :
      (Csmall z).val = F z.val :=
    (restrictCenteredEBallEquiv_val (ENNReal.ofReal_pos.mpr ρpos)
      (ENNReal.ofReal_le_ofReal (min_le_left ρ σ)) C' center_C' z).trans (agrees_C' _)
  refine ⟨radius, lt_min ρpos σpos, Csmall.trans Hsmall, ?_⟩
  intro z
  change place (Hsmall (Csmall z)).val = _
  have coordinates := restrictCenteredBallChart_val σpos (min_le_right ρ σ) H center_H (Csmall z)
  exact (congrArg place coordinates).trans
    ((agrees_H _).trans ((congrArg restored (agrees_small z)).trans (restores z.val)))

end Unfoldings
