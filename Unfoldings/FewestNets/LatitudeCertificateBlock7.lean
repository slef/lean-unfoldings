module

public import Unfoldings.FewestNets.LatitudeCertificateKernel
public import Mathlib.Tactic.FinCases

/-! Kernel validation of latitude enclosures 49 through 54. -/

@[expose] public section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

set_option maxRecDepth 200000
set_option maxHeartbeats 0

private theorem check49 (a : ℝ) (inside : (latitudeCertificateInterval 49).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 49) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check50 (a : ℝ) (inside : (latitudeCertificateInterval 50).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 50) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check51 (a : ℝ) (inside : (latitudeCertificateInterval 51).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 51) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check52 (a : ℝ) (inside : (latitudeCertificateInterval 52).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 52) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check53 (a : ℝ) (inside : (latitudeCertificateInterval 53).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 53) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check54 (a : ℝ) (inside : (latitudeCertificateInterval 54).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 54) inside nonneg = true := by
  latitude_certificate_rfl

theorem latitudeCertificateBlock7_checked (i : Fin 6) (a : ℝ)
    (inside : (latitudeCertificateInterval (49 + i.val)).Contains a) (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval (49 + i.val)) inside nonneg = true := by
  fin_cases i
  · exact check49 a inside nonneg
  · exact check50 a inside nonneg
  · exact check51 a inside nonneg
  · exact check52 a inside nonneg
  · exact check53 a inside nonneg
  · exact check54 a inside nonneg

end Unfoldings.FewestNets.RevisedLatitudeGrid
