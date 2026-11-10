module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.MeasureTheory.Group.AddCircle

/-! Canonical angular length on `Real.Angle`, inherited from its additive-circle model. -/

@[expose] public section

noncomputable section

namespace Real.Angle

open MeasureTheory

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

instance : CompactSpace Real.Angle := inferInstanceAs (CompactSpace (AddCircle (2 * Real.pi)))

instance : SecondCountableTopology Real.Angle :=
  inferInstanceAs (SecondCountableTopology (AddCircle (2 * Real.pi)))

instance : MeasureSpace Real.Angle := inferInstanceAs (MeasureSpace (AddCircle (2 * Real.pi)))

instance : BorelSpace Real.Angle := inferInstanceAs (BorelSpace (AddCircle (2 * Real.pi)))

instance : Measure.IsAddHaarMeasure (volume : Measure Real.Angle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure (volume : Measure (AddCircle (2 * Real.pi))))

instance : IsFiniteMeasure (volume : Measure Real.Angle) :=
  inferInstanceAs (IsFiniteMeasure (volume : Measure (AddCircle (2 * Real.pi))))

/-- A full turn has angular length `2π`. -/
theorem volume_univ : volume (Set.univ : Set Real.Angle) = ENNReal.ofReal (2 * Real.pi) :=
  AddCircle.measure_univ _

/-- Closed angular balls of radius at most pi have length twice their radius. -/
theorem volume_closedBall (θ : Real.Angle) {r : ℝ} (small : r ≤ Real.pi) :
    volume (Metric.closedBall θ r) = ENNReal.ofReal (2 * r) := by
  have formula := AddCircle.volume_closedBall (2 * Real.pi)
    (x := (show AddCircle (2 * Real.pi) from θ)) r
  exact formula.trans (congrArg ENNReal.ofReal (min_eq_right (by linarith)))

/-- Open angular balls have the same angular length as their closures. -/
theorem volume_ball (θ : Real.Angle) {r : ℝ} (small : r ≤ Real.pi) :
    volume (Metric.ball θ r) = ENNReal.ofReal (2 * r) := by
  have equal : (Metric.closedBall θ r : Set Real.Angle) =ᵐ[volume] Metric.ball θ r :=
    AddCircle.closedBall_ae_eq_ball
  rw [← measure_congr equal]
  exact volume_closedBall θ small

/-- Principal representatives have their usual real norm. -/
theorem norm_coe_eq_abs (t : ℝ) (small : |t| ≤ Real.pi) : ‖(t : Real.Angle)‖ = |t| := by
  change ‖(t : AddCircle (2 * Real.pi))‖ = |t|
  apply (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) (by positivity)).mpr
  rw [abs_of_pos Real.two_pi_pos]
  linarith

/-- The quotient-group norm is the absolute principal argument. -/
theorem norm_eq_abs_toReal (θ : Real.Angle) : ‖θ‖ = |θ.toReal| := by
  calc
    ‖θ‖ = ‖(θ.toReal : Real.Angle)‖ := by rw [coe_toReal]
    _ = |θ.toReal| := by
      change ‖(θ.toReal : AddCircle (2 * Real.pi))‖ = |θ.toReal|
      apply (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi)
        (by positivity : (2 * Real.pi : ℝ) ≠ 0)).mpr
      rw [abs_of_pos Real.two_pi_pos]
      linarith [abs_toReal_le_pi θ]

end Real.Angle
