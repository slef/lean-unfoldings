module

public import Unfoldings.FewestNets.LatitudeCertificateKernel
public import Mathlib.Tactic.FinCases

/-! Kernel validation of latitude enclosures 28 through 34. -/

@[expose] public section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

set_option maxRecDepth 200000
set_option maxHeartbeats 0

private theorem check28 (a : ℝ) (inside : (latitudeCertificateInterval 28).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 28) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check29 (a : ℝ) (inside : (latitudeCertificateInterval 29).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 29) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check30 (a : ℝ) (inside : (latitudeCertificateInterval 30).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 30) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check31 (a : ℝ) (inside : (latitudeCertificateInterval 31).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 31) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check32 (a : ℝ) (inside : (latitudeCertificateInterval 32).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 32) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check33 (a : ℝ) (inside : (latitudeCertificateInterval 33).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 33) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check34 (a : ℝ) (inside : (latitudeCertificateInterval 34).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 34) inside nonneg = true := by
  latitude_certificate_rfl

theorem latitudeCertificateBlock4_checked (i : Fin 7) (a : ℝ)
    (inside : (latitudeCertificateInterval (28 + i.val)).Contains a) (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval (28 + i.val)) inside nonneg = true := by
  fin_cases i
  · exact check28 a inside nonneg
  · exact check29 a inside nonneg
  · exact check30 a inside nonneg
  · exact check31 a inside nonneg
  · exact check32 a inside nonneg
  · exact check33 a inside nonneg
  · exact check34 a inside nonneg

end Unfoldings.FewestNets.RevisedLatitudeGrid
