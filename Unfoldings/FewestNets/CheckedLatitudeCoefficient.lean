module

public import Unfoldings.FewestNets.CheckedAnnularGridCharge

/-! Validate the normalized large-angle coefficient with fixed-point interval arithmetic. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real CheckedReal

local notation "D" => countPrecision
local notation "hD" => countPrecision_pos
local notation "Q" => CheckedReal.rat countPrecision

/-- The angular factor for the 0.115 separation of the annular selectors. -/
def tightAnnularPrefactor (a : ℝ) : ℝ :=
  2 / (cos (0.115 / 2) ^ 2 * sin (2 * a))

/-- Normalize the expected total count by the fourth power of the margin. -/
def normalizedGridCoefficient (a : ℝ) : ℝ :=
  2 * a ^ 4 + 4.90 * a ^ 2 + tightAnnularPrefactor a * gridCharge a * a ^ 4

theorem gridCharge_nonneg {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    0 ≤ gridCharge a := by
  rw [gridCharge_eq_sum positive small]
  apply Finset.sum_nonneg
  intro i _
  unfold annularAlgebraicCharge
  apply le_max_of_le_right
  apply div_nonneg _ (by positivity)
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (sqrt_nonneg _) (by
    unfold shortSideRatio annularSineSquared
    positivity))

def checkAnnularPrefactor {a : ℝ} (input : CheckedCount a) :
    CheckedCount (tightAnnularPrefactor a) := by
  let tw := ((Q 2).mul hD input).checkSinCentered hD 24
  let c := (Q 0.0575).checkCosCentered hD 24
  exact ((Q 2).div hD ((c.square hD).mul hD tw)).convert (by norm_num [tightAnnularPrefactor])

def checkNormalizedCoefficient {a : ℝ} (input : CheckedCount a) (nonneg : 0 ≤ gridCharge a) :
    CheckedCount (normalizedGridCoefficient a) := by
  let sq := input.square hD
  let fourth := sq.square hD
  let area := (Q 2).mul hD fourth
  let poles := (Q 4.90).mul hD sq
  let annulus := ((checkAnnularPrefactor input).mul hD
    ((checkGridCharge input).nonnegative nonneg)).mul hD fourth
  exact ((area.add poles).add annulus).convert (by norm_num [normalizedGridCoefficient]; ring)

def intervalCoefficientTest (A : CountInterval) {a : ℝ}
    (inside : A.Contains a) (nonneg : 0 ≤ gridCharge a) : Bool :=
  (checkNormalizedCoefficient (enclose A inside) nonneg).isLT (Q 246.3)

theorem normalizedGridCoefficient_lt_of_check {a : ℝ} {A : CountInterval}
    (inside : A.Contains a) (nonneg : 0 ≤ gridCharge a)
    (checked : intervalCoefficientTest A inside nonneg = true) :
    normalizedGridCoefficient a < 246.3 := by
  have h := lt_of_isLT hD _ _ checked
  exact h.trans_eq (by norm_num)

end Unfoldings.FewestNets.RevisedLatitudeGrid
