module

public import Unfoldings.FewestNets.LatitudeCertificateKernel
public import Mathlib.Tactic.FinCases

/-! Kernel validation of latitude enclosures 21 through 27. -/

@[expose] public section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

set_option maxRecDepth 200000
set_option maxHeartbeats 0

private theorem check21 (a : ℝ) (inside : (latitudeCertificateInterval 21).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 21) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check22 (a : ℝ) (inside : (latitudeCertificateInterval 22).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 22) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check23 (a : ℝ) (inside : (latitudeCertificateInterval 23).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 23) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check24 (a : ℝ) (inside : (latitudeCertificateInterval 24).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 24) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check25 (a : ℝ) (inside : (latitudeCertificateInterval 25).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 25) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check26 (a : ℝ) (inside : (latitudeCertificateInterval 26).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 26) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check27 (a : ℝ) (inside : (latitudeCertificateInterval 27).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 27) inside nonneg = true := by
  latitude_certificate_rfl

theorem latitudeCertificateBlock3_checked (i : Fin 7) (a : ℝ)
    (inside : (latitudeCertificateInterval (21 + i.val)).Contains a) (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval (21 + i.val)) inside nonneg = true := by
  fin_cases i
  · exact check21 a inside nonneg
  · exact check22 a inside nonneg
  · exact check23 a inside nonneg
  · exact check24 a inside nonneg
  · exact check25 a inside nonneg
  · exact check26 a inside nonneg
  · exact check27 a inside nonneg

end Unfoldings.FewestNets.RevisedLatitudeGrid
