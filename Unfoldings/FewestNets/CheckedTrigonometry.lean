module

public import Unfoldings.FewestNets.CheckedReal
public import Unfoldings.FewestNets.TaylorEnclosures
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Computable sine and cosine interval certificates with proved Taylor remainders. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.CheckedReal

open Real
open scoped Nat

variable {D : ℕ} {x y r : ℝ}

/-- Extend a checked approximation by an error radius. -/
def withError (a : CheckedReal D x) (e : CheckedReal D r) (error : |y - x| ≤ r) :
    CheckedReal D y :=
  map₂ (fun a b => some ⟨a.lo - b.hi, a.hi + b.hi⟩) (by
    intro lo hi result hx he h
    cases h
    have h₁ := mul_le_mul_of_nonneg_right (abs_le.mp error).1 (Nat.cast_nonneg D)
    have h₂ := mul_le_mul_of_nonneg_right (abs_le.mp error).2 (Nat.cast_nonneg D)
    change ((lo.lo - hi.hi : ℤ) : ℝ) ≤ y * D ∧ y * D ≤ ((lo.hi + hi.hi : ℤ) : ℝ)
    push_cast
    exact ⟨by linarith only [hx.1, he.2, h₁], by linarith only [hx.2, he.2, h₂]⟩) a e

def pow (hD : 0 < D) (a : CheckedReal D x) (n : ℕ) : CheckedReal D (x ^ n) :=
  match n with
  | 0 => (rat D 1).convert (by simp)
  | n + 1 => ((pow hD a n).mul hD a).convert (pow_succ x n).symm

/-- Use Mathlib's proved twenty-place bounds on pi directly. -/
def checkPi (D : ℕ) : CheckedReal D π where
  bounds := some ⟨(FixedPointInterval.ofRat D 3.14159265358979323846).lo,
    (FixedPointInterval.ofRat D 3.14159265358979323847).hi⟩
  sound _ h := by
    cases h
    have lo := (FixedPointInterval.contains_ofRat (D := D) 3.14159265358979323846).1
    have hi := (FixedPointInterval.contains_ofRat (D := D) 3.14159265358979323847).2
    refine ⟨lo.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg D)),
      (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg D)).trans hi⟩
    · exact_mod_cast pi_gt_d20.le
    · exact_mod_cast pi_lt_d20.le

def checkTaylorTerm (hD : 0 < D) (a : CheckedReal D x) (coefficient : ℕ → ℤ) (k : ℕ) :
    CheckedReal D (((coefficient k : ℝ) / (k ! : ℝ)) * x ^ k) :=
  ((rat D ((coefficient k : ℚ) / (k ! : ℚ))).convert (by simp)).mul hD (a.pow hD k)

def checkIntegerTaylor (hD : 0 < D) (a : CheckedReal D x) (coefficient : ℕ → ℤ) (n : ℕ) :
    CheckedReal D (integerTaylor coefficient n x) :=
  match n with
  | 0 => (a.checkTaylorTerm hD coefficient 0).convert (by simp [integerTaylor])
  | n + 1 => ((checkIntegerTaylor hD a coefficient n).add
    (a.checkTaylorTerm hD coefficient (n + 1))).convert (by
      unfold integerTaylor
      exact (Finset.sum_range_succ (fun k => ((coefficient k : ℝ) / (k ! : ℝ)) * x ^ k)
        (n + 1)).symm)

def checkTaylorRadius (hD : 0 < D) (a : CheckedReal D x) (n : ℕ) :
    CheckedReal D (|x| ^ (n + 1) / ((n + 1)! : ℝ)) :=
  ((a.abs hD).pow hD (n + 1)).div hD ((rat D ((n + 1)! : ℚ)).convert (by simp))

def checkSin (hD : 0 < D) (a : CheckedReal D x) (n : ℕ) : CheckedReal D (sin x) :=
  (a.checkIntegerTaylor hD sinCoefficient n).withError (a.checkTaylorRadius hD n)
    (abs_sin_sub_integerTaylor_le n x)

def checkCos (hD : 0 < D) (a : CheckedReal D x) (n : ℕ) : CheckedReal D (cos x) :=
  (a.checkIntegerTaylor hD cosCoefficient n).withError (a.checkTaylorRadius hD n)
    (abs_cos_sub_integerTaylor_le n x)

end Unfoldings.FewestNets.CheckedReal
