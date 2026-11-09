module

public import Unfoldings.Path.Length

/-! Intrinsic distance as the infimum of lengths of all continuous paths. -/

@[expose] public section

open scoped ENNReal

namespace Path

variable {X : Type*} [PseudoEMetricSpace X]

/-- Continuous-path distance, infinite if no rectifiable path joins the endpoints. -/
noncomputable def eDistance (a b : X) : ℝ≥0∞ := ⨅ p : Path a b, p.eLength

theorem eDistance_le_eLength {a b : X} (p : Path a b) : eDistance a b ≤ p.eLength := iInf_le _ p

theorem edist_le_eDistance (a b : X) : edist a b ≤ eDistance a b :=
  le_iInf fun p => p.edist_le_eLength

@[simp] theorem eDistance_self (a : X) : eDistance a a = 0 :=
  le_antisymm ((eDistance_le_eLength (Path.refl a)).trans_eq (eLength_refl a)) bot_le

theorem eDistance_comm (a b : X) : eDistance a b = eDistance b a := by
  have bound (x y : X) : eDistance x y ≤ eDistance y x := by
    apply le_iInf
    intro p
    simpa only [eLength_symm] using eDistance_le_eLength p.symm
  exact le_antisymm (bound a b) (bound b a)

theorem eDistance_triangle (a b c : X) : eDistance a c ≤ eDistance a b + eDistance b c := by
  apply ENNReal.le_iInf_add_iInf
  intro p q
  simpa only [eLength_trans] using eDistance_le_eLength (p.trans q)

theorem IsLengthMinimizing.eLength_eq_eDistance {a b : X} {p : Path a b}
    (minimal : p.IsLengthMinimizing) : p.eLength = eDistance a b :=
  le_antisymm (le_iInf minimal) p.eDistance_le_eLength

end Path
