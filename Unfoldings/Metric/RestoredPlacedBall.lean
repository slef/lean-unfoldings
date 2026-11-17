module

public import Unfoldings.Metric.PlacedBallComposition

/-! Whole physical model charts survive local restoration in either direction. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings

variable {X Y Z S : Type*} [EMetricSpace X] [EMetricSpace Y] [MetricSpace Z]

/-- Transport a physically placed model chart to a restored cut using the inverse of its
whole-ball restoration chart. The canonical fold, original model and center are retained. -/
theorem exists_restored_placed_ball_chart (F : X → Y) (original : X → S) (restored : Y → S)
    (place : Z → S) (injective : Function.Injective place) {x : X} {a : Z}
    (restores : ∀ z, restored (F z) = original z)
    {ρ σ : ℝ} (ρpos : 0 < ρ) (σpos : 0 < σ)
    (C : Metric.eball x (ENNReal.ofReal ρ) ≃ᵢ Metric.eball (F x) (ENNReal.ofReal ρ))
    (agrees_C : ∀ z, (C z).val = F z.val)
    (H : Metric.eball x (ENNReal.ofReal σ) ≃ᵢ Metric.ball a σ)
    (agrees_H : ∀ z, place (H z).val = original z.val)
    (model_place : place a = original x) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ D : Metric.eball (F x) (ENNReal.ofReal ε) ≃ᵢ Metric.ball a ε,
      ∀ z, place (D z).val = restored z.val := by
  have center_C : (C ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr ρpos)⟩).val = F x :=
    agrees_C _
  have center_H : (H ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr σpos)⟩).val = a :=
    injective ((agrees_H _).trans model_place.symm)
  let radius := min ρ σ
  let Csmall := restrictCenteredEBallEquiv (ENNReal.ofReal_pos.mpr ρpos)
    (ENNReal.ofReal_le_ofReal (min_le_left ρ σ)) C center_C
  let Hsmall := restrictCenteredBallChart σpos (min_le_right ρ σ) H center_H
  have agrees_small (z : Metric.eball x (ENNReal.ofReal radius)) :
      (Csmall z).val = F z.val :=
    (restrictCenteredEBallEquiv_val (ENNReal.ofReal_pos.mpr ρpos)
      (ENNReal.ofReal_le_ofReal (min_le_left ρ σ)) C center_C z).trans (agrees_C _)
  refine ⟨radius, lt_min ρpos σpos, Csmall.symm.trans Hsmall, ?_⟩
  intro z
  have inverse : F (Csmall.symm z).val = z.val :=
    (agrees_small (Csmall.symm z)).symm.trans
      (congrArg Subtype.val (Csmall.apply_symm_apply z))
  exact (congrArg place (restrictCenteredBallChart_val σpos (min_le_right ρ σ) H center_H
    (Csmall.symm z))).trans
    ((agrees_H _).trans ((restores (Csmall.symm z).val).symm.trans (congrArg restored inverse)))

end Unfoldings
