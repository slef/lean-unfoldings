module

public import Unfoldings.FewestNets.CheckedDevelopment

/-! Exact scalar validation of one finite routing and development record. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real CheckedReal

/-- The scalar fields of a finite progress-body certificate. Angles in degrees are
kept rational until converted to radians in a check. -/
structure DevelopmentScalarRecord where
  tilt : ℚ
  visualAngleDegrees : ℚ
  cotangent : ℚ
  margin : ℚ
  lengthConstant : ℚ

namespace DevelopmentScalarRecord

def ValidFor (r : DevelopmentScalarRecord) (targetDegrees : ℚ) : Prop :=
  0 < r.tilt ∧ r.tilt < 1 ∧ targetDegrees < r.visualAngleDegrees ∧
    r.visualAngleDegrees < 90 ∧ 0 < r.cotangent ∧ 0 < r.margin ∧ r.margin < 1 ∧ 0 < r.lengthConstant

instance (r : DevelopmentScalarRecord) (targetDegrees : ℚ) :
    Decidable (r.ValidFor targetDegrees) := by
  unfold ValidFor
  infer_instance

theorem tan_half_sq_lt_one_of_lt_one {φ : ℝ} (positive : 0 ≤ φ) (small : φ < 1) :
    tan (φ / 2) ^ 2 < 1 := by
  have h : φ / 2 < π / 4 := by linarith only [small, Real.pi_gt_three]
  have lo : 0 ≤ φ / 2 := by positivity
  have t : tan (φ / 2) < 1 := by
    rw [← tan_pi_div_four]
    exact Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two lo (by linarith only [pi_pos]) h
  have nonneg : 0 ≤ tan (φ / 2) :=
    tan_nonneg_of_nonneg_of_le_pi_div_two lo (by linarith only [h, pi_pos])
  simpa only [one_pow] using (sq_lt_sq₀ nonneg zero_le_one).mpr t

theorem tan_half_sq_lt_one (r : DevelopmentScalarRecord) {target : ℚ} (valid : r.ValidFor target) :
    tan ((r.tilt : ℝ) / 2) ^ 2 < 1 :=
  tan_half_sq_lt_one_of_lt_one (by exact_mod_cast valid.1.le) (by exact_mod_cast valid.2.1)

theorem margin_nonneg (r : DevelopmentScalarRecord) {target : ℚ} (valid : r.ValidFor target) :
    (0 : ℝ) ≤ r.margin := by exact_mod_cast valid.2.2.2.2.2.1.le

theorem margin_lt_one (r : DevelopmentScalarRecord) {target : ℚ} (valid : r.ValidFor target) :
    (r.margin : ℝ) < 1 := by exact_mod_cast valid.2.2.2.2.2.2.1

def cotangentGap (r : DevelopmentScalarRecord) : ℝ :=
  let complement := (90 - (r.visualAngleDegrees : ℝ)) * π / 180
  sin complement - (r.cotangent : ℝ) * cos complement

def interiorMarginGap (r : DevelopmentScalarRecord) (targetDegrees : ℚ) : ℝ :=
  sin (((r.visualAngleDegrees : ℝ) - targetDegrees) * π / 360 -
    arcsin (tan ((r.tilt : ℝ) / 2) ^ 2)) - r.margin

def checkCotangentGap (r : DevelopmentScalarRecord) {D : ℕ} (hD : 0 < D) :
    CheckedReal D r.cotangentGap :=
  let complement := ((rat D (90 - r.visualAngleDegrees)).mul hD (checkPi D)).div hD
    (rat D 180)
  ((complement.checkSin hD 12).sub ((rat D r.cotangent).mul hD
    (complement.checkCos hD 12))).convert (by simp [cotangentGap])

def checkInteriorMarginGap (r : DevelopmentScalarRecord) {D : ℕ} (hD : 0 < D)
    {targetDegrees : ℚ} (valid : r.ValidFor targetDegrees) :
    CheckedReal D (r.interiorMarginGap targetDegrees) :=
  let halfAngle := ((rat D (r.visualAngleDegrees - targetDegrees)).mul hD (checkPi D)).div hD
    (rat D 360)
  let tiltHalf := (rat D r.tilt).div hD (rat D 2)
  let tanSquared := (tiltHalf.checkTan hD 12).square hD
  let delta := tanSquared.checkArcsin hD (sq_nonneg _) (by
    simpa using r.tan_half_sq_lt_one valid)
  (((halfAngle.sub delta).checkSin hD 12).sub (rat D r.margin)).convert
    (by simp [interiorMarginGap])

def checkGaps (r : DevelopmentScalarRecord) {D : ℕ} (hD : 0 < D)
    {targetDegrees : ℚ} (valid : r.ValidFor targetDegrees) :
    (i : Fin 3) → CheckedReal D (developmentGaps r.tilt r.margin r.lengthConstant i) :=
  checkDevelopmentGaps hD (rat D r.tilt) (rat D r.margin) (rat D r.lengthConstant)
    (r.tan_half_sq_lt_one valid) (r.margin_nonneg valid) (r.margin_lt_one valid) 12

/-- Recheck the three development gaps and the visual and interior margin gaps. -/
def check (r : DevelopmentScalarRecord) {D : ℕ} (hD : 0 < D) (targetDegrees : ℚ) : Bool :=
  if h : r.ValidFor targetDegrees then
    (List.finRange 3).all (fun i => (r.checkGaps hD h i).isPositive) &&
      ((r.checkCotangentGap hD).isPositive && (r.checkInteriorMarginGap hD h).isPositive)
  else false

theorem bounds_of_check (r : DevelopmentScalarRecord) {D : ℕ} (hD : 0 < D)
    (targetDegrees : ℚ) (pass : r.check hD targetDegrees = true) :
    r.ValidFor targetDegrees ∧
      (∀ i : Fin 3, 0 < developmentGaps r.tilt r.margin r.lengthConstant i) ∧
      0 < r.cotangentGap ∧ 0 < r.interiorMarginGap targetDegrees := by
  unfold check at pass
  split at pass
  · rename_i h
    simp only [Bool.and_eq_true] at pass
    exact ⟨h, fun i => positive_of_isPositive hD (r.checkGaps hD h i)
      (List.all_eq_true.mp pass.1 i (List.mem_finRange i)),
      positive_of_isPositive hD _ pass.2.1, positive_of_isPositive hD _ pass.2.2⟩
  · simp at pass

end DevelopmentScalarRecord
end Unfoldings.FewestNets
