module

public import Unfoldings.FewestNets.LatitudeCertificateKernel
public import Mathlib.Tactic.FinCases

/-! Kernel validation of latitude enclosures 42 through 48. -/

@[expose] public section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

set_option maxRecDepth 200000
set_option maxHeartbeats 0

private theorem check42 (a : ℝ) (inside : (latitudeCertificateInterval 42).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 42) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check43 (a : ℝ) (inside : (latitudeCertificateInterval 43).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 43) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check44 (a : ℝ) (inside : (latitudeCertificateInterval 44).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 44) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check45 (a : ℝ) (inside : (latitudeCertificateInterval 45).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 45) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check46 (a : ℝ) (inside : (latitudeCertificateInterval 46).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 46) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check47 (a : ℝ) (inside : (latitudeCertificateInterval 47).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 47) inside nonneg = true := by
  latitude_certificate_rfl

private theorem check48 (a : ℝ) (inside : (latitudeCertificateInterval 48).Contains a)
    (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval 48) inside nonneg = true := by
  latitude_certificate_rfl

theorem latitudeCertificateBlock6_checked (i : Fin 7) (a : ℝ)
    (inside : (latitudeCertificateInterval (42 + i.val)).Contains a) (nonneg : 0 ≤ gridCharge a) :
    intervalCoefficientTest (latitudeCertificateInterval (42 + i.val)) inside nonneg = true := by
  fin_cases i
  · exact check42 a inside nonneg
  · exact check43 a inside nonneg
  · exact check44 a inside nonneg
  · exact check45 a inside nonneg
  · exact check46 a inside nonneg
  · exact check47 a inside nonneg
  · exact check48 a inside nonneg

end Unfoldings.FewestNets.RevisedLatitudeGrid
