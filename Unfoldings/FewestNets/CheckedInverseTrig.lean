module

public import Unfoldings.FewestNets.CheckedTrigonometry
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Certified enclosures of the small inverse trigonometric expressions in development. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.CheckedReal

open Real

variable {D : ℕ} {x y z : ℝ}

/-- Keep the lower endpoint from one enclosure and the upper endpoint from another. -/
def between (lower : CheckedReal D x) (upper : CheckedReal D z)
    (xl : x ≤ y) (yu : y ≤ z) : CheckedReal D y :=
  map₂ (fun a b => some ⟨a.lo, b.hi⟩) (by
    intro a b c ha hb h
    cases h
    exact ⟨ha.1.trans (mul_le_mul_of_nonneg_right xl (Nat.cast_nonneg D)),
      (mul_le_mul_of_nonneg_right yu (Nat.cast_nonneg D)).trans hb.2⟩) lower upper

theorem le_arcsin_of_nonneg (positive : 0 ≤ x) (small : x ≤ 1) : x ≤ arcsin x := by
  have h : 0 ≤ arcsin x := by rw [← arcsin_zero]; exact arcsin_le_arcsin positive
  have key := Real.sin_le h
  rwa [sin_arcsin (by linarith) small] at key

theorem arcsin_le_div_sqrt (positive : 0 ≤ x) (small : x < 1) :
    arcsin x ≤ x / Real.sqrt (1 - x ^ 2) := by
  have h : 0 ≤ arcsin x := by rw [← arcsin_zero]; exact arcsin_le_arcsin positive
  have strict : arcsin x < π / 2 :=
    lt_of_not_ge (fun n => small.not_ge (pi_div_two_le_arcsin.mp n))
  exact (le_tan h strict).trans_eq (tan_arcsin x)

/-- The endpoints use the sine and tangent of the same inverse-sine angle.
At the small inputs of the development theorem the enclosure is narrow. -/
def checkArcsin (hD : 0 < D) (a : CheckedReal D x) (positive : 0 ≤ x) (small : x < 1) :
    CheckedReal D (arcsin x) :=
  let one : CheckedReal D (1 : ℝ) := (rat D 1).convert (by simp)
  let upper := a.div hD ((one.sub (a.square hD)).sqrt hD)
  a.between upper (le_arcsin_of_nonneg positive small.le) (arcsin_le_div_sqrt positive small)

/-- Evaluate sine and cosine of the same argument with a common Taylor order. -/
def checkTan (hD : 0 < D) (a : CheckedReal D x) (order : ℕ) : CheckedReal D (tan x) :=
  ((a.checkSin hD order).div hD (a.checkCos hD order)).convert (tan_eq_sin_div_cos x).symm

end Unfoldings.FewestNets.CheckedReal
