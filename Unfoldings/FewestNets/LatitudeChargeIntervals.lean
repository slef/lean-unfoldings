module

public import Unfoldings.FewestNets.CheckedIntervalGrid
public import Unfoldings.FewestNets.TightAnnularCharge

/-! The finite interval check for the arclength and determinant charge of one triangle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real CheckedReal

/-- All certificate endpoints are scaled by the same positive integer. -/
abbrev countPrecision : ℕ := 10 ^ 14

abbrev CountInterval := FixedPointInterval countPrecision

local notation "Q" => FixedPointInterval.ofRat countPrecision
local notation "Crat" => CheckedReal.rat countPrecision

theorem countPrecision_pos : 0 < countPrecision := by decide

/-- The chord polynomial is increasing on the range of the short side. -/
theorem chordSineSquared_mono {x y : ℝ} (_hx : 0 ≤ x) (hy : y ≤ 2) (hxy : x ≤ y) :
    x * (1 - x / 4) ≤ y * (1 - y / 4) := by
  have positive : 0 ≤ 1 - (y + x) / 4 := by linarith only [hy, hxy]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hxy) positive]

/-- Use the upper chord endpoint in the exact monotone squared-sine formula. -/
def chordSineSquaredInterval (d : CountInterval) : Option CountInterval :=
  if 0 ≤ d.hi ∧ d.hi ≤ (2 : ℤ) * countPrecision then
    let high : CountInterval := ⟨d.hi, d.hi⟩
    let value := high.mul ((Q 1).sub (high.mul (Q (1 / 4))))
    some ⟨0, value.hi⟩
  else none

theorem chordSineSquaredInterval_sound {d out : CountInterval} {x : ℝ}
    (hx : d.Contains x) (x0 : 0 ≤ x) (checked : chordSineSquaredInterval d = some out) :
    out.Contains (x * (1 - x / 4)) := by
  unfold chordSineSquaredInterval at checked
  split at checked
  · rename_i valid
    obtain rfl := (Option.some.inj checked).symm
    let v := (d.hi : ℝ) / countPrecision
    have dp := FixedPointInterval.cast_den_pos countPrecision_pos
    have hv : x ≤ v := (le_div_iff₀ dp).mpr hx.2
    have hvalid : (d.hi : ℝ) ≤ (200000000000000 : ℤ) := Int.cast_le.mpr valid.2
    have range : v ≤ 2 := (div_le_iff₀ dp).mpr (by norm_num [countPrecision] at hvalid ⊢; exact hvalid)
    have point : (⟨d.hi, d.hi⟩ : CountInterval).Contains v := by
      unfold FixedPointInterval.Contains
      dsimp only [v]
      rw [div_mul_cancel₀ _ dp.ne']
      exact ⟨le_rfl, le_rfl⟩
    have scaled := FixedPointInterval.contains_mul countPrecision_pos point (FixedPointInterval.contains_ofRat (D := countPrecision) (1 / 4))
    have one := FixedPointInterval.contains_ofRat (D := countPrecision) 1
    have high := FixedPointInterval.contains_mul countPrecision_pos point (FixedPointInterval.contains_sub one scaled)
    have upper : x * (1 - x / 4) ≤ v * (1 - v * ((1 / 4 : ℚ) : ℝ)) := by
      push_cast
      simpa only [div_eq_mul_inv, one_mul] using chordSineSquared_mono x0 range hv
    have hpos : 0 ≤ 1 - x / 4 := by linarith only [hv, range]
    refine ⟨?_, ?_⟩
    · simp only [Int.cast_zero]
      exact mul_nonneg (mul_nonneg x0 hpos) dp.le
    · exact (mul_le_mul_of_nonneg_right upper dp.le).trans (by simpa only [Rat.cast_one] using high.2)
  · simp at checked

/-- Typed form of the same interval operation. -/
def checkChordSineSquared {x : ℝ} (d : CheckedReal countPrecision x) (x0 : 0 ≤ x) :
    CheckedReal countPrecision (x * (1 - x / 4)) :=
  d.map chordSineSquaredInterval (fun h eq => chordSineSquaredInterval_sound h x0 eq)

/-- The short-side polynomial is evaluated on a squared sine. -/
def checkShortSideRatio {x : ℝ} (i : CheckedReal countPrecision x) :
    CheckedReal countPrecision (shortSideRatio x) :=
  ((Crat 1).add (i.mul countPrecision_pos (Crat (1 / 6)))).add
    (i.square countPrecision_pos |>.mul countPrecision_pos (Crat (1 / 10))) |>.convert (by
      unfold shortSideRatio
      push_cast
      ring)

/-- Add the three real summands in the order used by the certificate. -/
def checkFinThreeSum {x : Fin 3 → ℝ} (i : ∀ j, CheckedReal countPrecision (x j)) :
    CheckedReal countPrecision (∑ j, x j) :=
  (((i 0).add (i 1)).add (i 2)).convert (Fin.sum_univ_three x).symm

/-- Evaluate the two finite crossing-charge alternatives from the
squared side sines and the signed determinant. -/
def checkTriangleCharge {s : Fin 3 → ℝ} {det : ℝ}
    (side : ∀ j, CheckedReal countPrecision (s j)) (area : CheckedReal countPrecision det) :
    CheckedReal countPrecision
      (max ((2 / π) * shortSideRatio (max (s 0) (max (s 1) (s 2))) *
        ((∑ j : Fin 3, √(s j * s (j + 2))) / |det|))
        ((∑ j : Fin 3, √(s j) * shortSideRatio (s j)) / (π * 0.115))) := by
  exact (side 0).reuse fun s0 =>
    (side 1).reuse fun s1 =>
    (side 2).reuse fun s2 =>
    area.reuse fun area' => by
      let side' (j : Fin 3) : CheckedReal countPrecision (s j) :=
        if h₀ : j = 0 then s0.convert (congrArg s h₀.symm)
        else if h₁ : j = 1 then s1.convert (congrArg s h₁.symm)
        else s2.convert (congrArg s (show 2 = j by
          apply Fin.ext
          have l := j.isLt
          have b : j.val ≠ 0 := fun h => h₀ (Fin.ext h)
          have c : j.val ≠ 1 := fun h => h₁ (Fin.ext h)
          change 2 = j.val
          omega))
      let p := checkPi countPrecision
      let largest := s0.maximum countPrecision_pos (s1.maximum countPrecision_pos s2)
      let factor := ((Crat 2).div countPrecision_pos p).mul countPrecision_pos (checkShortSideRatio largest)
      let products := checkFinThreeSum (fun j : Fin 3 =>
        ((side' j).mul countPrecision_pos (side' (j + 2))).sqrt countPrecision_pos)
      let angles := factor.mul countPrecision_pos (products.div countPrecision_pos (area'.abs countPrecision_pos))
      let lengths := checkFinThreeSum (fun j : Fin 3 => ((side' j).sqrt countPrecision_pos).mul countPrecision_pos
        (checkShortSideRatio (side' j)))
      let perimeter := lengths.div countPrecision_pos (p.mul countPrecision_pos (Crat 0.115))
      exact (angles.maximum countPrecision_pos perimeter).convert (by norm_num)

end Unfoldings.FewestNets.RevisedLatitudeGrid
