module

public import Unfoldings.FewestNets.LatitudeCertificateBlock3
public import Unfoldings.FewestNets.LatitudeCertificateBlock4
public import Unfoldings.FewestNets.LatitudeCertificateBlock5
public import Unfoldings.FewestNets.LatitudeCertificateBlock6
public import Unfoldings.FewestNets.LatitudeCertificateBlock7

/-! The checked intervals prove the large-angle bound for the actual latitude grid. -/

@[expose] public section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real

private theorem test_eq_of_index_eq {i j : ℕ} (h : i = j) (a : ℝ) (nonneg : 0 ≤ gridCharge a)
    (inside₁ : (latitudeCertificateInterval i).Contains a) (inside₂ : (latitudeCertificateInterval j).Contains a) :
    intervalCoefficientTest (latitudeCertificateInterval i) inside₁ nonneg =
      intervalCoefficientTest (latitudeCertificateInterval j) inside₂ nonneg := by
  subst j
  rfl

/-- Every interval in the finite cover passes the count check. -/
theorem latitudeCertificate_checked (k : Fin 55) (first : 21 ≤ k.val) (a : ℝ) (nonneg : 0 ≤ gridCharge a)
    (inside : (latitudeCertificateInterval k.val).Contains a) :
    intervalCoefficientTest (latitudeCertificateInterval k.val) inside nonneg = true := by
  have check_block (start length : ℕ) (lo : start ≤ k.val) (hi : k.val < start + length)
      (valid : ∀ (j : Fin length) (a : ℝ)
        (here : (latitudeCertificateInterval (start + j.val)).Contains a) (p : 0 ≤ gridCharge a),
        intervalCoefficientTest (latitudeCertificateInterval (start + j.val)) here p = true) :
      intervalCoefficientTest (latitudeCertificateInterval k.val) inside nonneg = true := by
    let j : Fin length := ⟨k.val - start, by omega⟩
    have eq : start + j.val = k.val := by
      change start + (k.val - start) = k.val
      omega
    have here : (latitudeCertificateInterval (start + j.val)).Contains a := eq.symm ▸ inside
    rw [← test_eq_of_index_eq eq a nonneg here inside]
    exact valid j a here nonneg
  have upper := k.isLt
  by_cases h₃ : k.val < 28
  · exact check_block 21 7 (by omega) (by omega) latitudeCertificateBlock3_checked
  by_cases h₄ : k.val < 35
  · exact check_block 28 7 (by omega) (by omega) latitudeCertificateBlock4_checked
  by_cases h₅ : k.val < 42
  · exact check_block 35 7 (by omega) (by omega) latitudeCertificateBlock5_checked
  by_cases h₆ : k.val < 49
  · exact check_block 42 7 (by omega) (by omega) latitudeCertificateBlock6_checked
  · exact check_block 49 6 (by omega) (by omega) latitudeCertificateBlock7_checked

/-- The verified normalized coefficient is below 246.3 on the large-angle range. -/
theorem normalizedGridCoefficient_lt {a : ℝ} (lower : 0.415 ≤ a) (upper : a ≤ π / 6) :
    normalizedGridCoefficient a < 246.3 := by
  obtain ⟨k, first, inside⟩ := exists_latitudeCertificateInterval lower upper
  have positive : 0 < a := by linarith only [lower]
  have nonneg := gridCharge_nonneg positive upper
  exact normalizedGridCoefficient_lt_of_check inside nonneg (latitudeCertificate_checked k first a nonneg inside)

end Unfoldings.FewestNets.RevisedLatitudeGrid
