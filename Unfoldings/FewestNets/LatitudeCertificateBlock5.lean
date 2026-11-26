module

public import Unfoldings.FewestNets.LatitudeCertificateKernel
public import Mathlib.Tactic.FinCases

/-! Kernel validation of latitude enclosures 35 through 41. -/

@[expose] public section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

set_option maxRecDepth 200000
set_option maxHeartbeats 0

private theorem check35 (a : ℝ) (inside : (latitudeCertificateInterval 35).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 35) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check36 (a : ℝ) (inside : (latitudeCertificateInterval 36).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 36) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check37 (a : ℝ) (inside : (latitudeCertificateInterval 37).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 37) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check38 (a : ℝ) (inside : (latitudeCertificateInterval 38).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 38) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check39 (a : ℝ) (inside : (latitudeCertificateInterval 39).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 39) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check40 (a : ℝ) (inside : (latitudeCertificateInterval 40).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 40) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check41 (a : ℝ) (inside : (latitudeCertificateInterval 41).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 41) inside nonneg = true := by
  latitude_certificate_rfl

theorem latitudeCertificateBlock5_checked (i : Fin 7) (a : ℝ)
    (inside : (latitudeCertificateInterval (35 + i.val)).Contains a) (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval (35 + i.val)) inside nonneg = true := by
  fin_cases i
  · exact check35 a inside nonneg
  · exact check36 a inside nonneg
  · exact check37 a inside nonneg
  · exact check38 a inside nonneg
  · exact check39 a inside nonneg
  · exact check40 a inside nonneg
  · exact check41 a inside nonneg

end Unfoldings.FewestNets.RevisedLatitudeGrid
