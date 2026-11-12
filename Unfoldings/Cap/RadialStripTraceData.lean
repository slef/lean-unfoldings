module

public import Unfoldings.Cap.RadialBankTraceProperty
public import Unfoldings.Cap.MatchedBankTrace
public import Unfoldings.Cap.CenteredTraceValues
public import Unfoldings.Geometry.RecoverableStripPinches

/-! Retain one radial trace's source, coherent pinches, visibility, and geometry together. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)
  {t : ℝ} (positive : 0 < t) (small : t < 1)
  (D : FacewiseDevelopment C N.retain) (calibration : Plane ≃ₗᵢ[ℝ] ℂ)
  (i : FiveSector) (S : MonotoneStrip) (ε cutoff : ℝ)

/-- Proved output of the actual waterfall construction. In particular, the coherent
pinch set, complete bank values, and source normalization belong to this same strip. -/
structure RadialStripTraceData where
  coherentSet : Set ℂ
  finite_coherentSet : coherentSet.Finite
  source_mem : (0 : ℂ) ∈ coherentSet
  lower_source : S.lower.coordinate 0 = 0
  upper_source : S.upper.coordinate 0 = 0
  pinches : S.RecoverablePinchesIn coherentSet 0 cutoff
  physical : ∀ z, (z ∈ S.strictCarrier ∨ z ∈ coherentSet) → z.re + z.im ∈ Set.Icc 0 cutoff →
    source + (fiveSectorFrame t positive small i).place.symm z ∈ K.footprint ∧
      D.ProjectedCoherentAt K (source + (fiveSectorFrame t positive small i).place.symm z)
  avoids_cuts : ∀ z ∈ S.strictCarrier, z.re + z.im ∈ Set.Icc 0 cutoff →
    source + (fiveSectorFrame t positive small i).place.symm z ∉ cuts
  value : ℂ → ℂ
  continuous : Continuous value
  equal : Set.EqOn
    (D.centeredMap K source calibration (fiveSectorFrame t positive small i).place) value
    {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff}
  strict_injective : Set.InjOn
    (D.centeredMap K source calibration (fiveSectorFrame t positive small i).place)
    {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff}
  closed_injective : Set.InjOn value
    (closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff})
  radial : S.RadialBankTraces value
    (D.centeredMap K source calibration (fiveSectorFrame t positive small i).place 0) cutoff
  bank_matching : N.MatchesParentBanks positive small i (N.completedDevelopment D)
    calibration value S cutoff
  source_error : ∀ z ∈ S.strictCarrier, z.re + z.im ∈ Set.Icc 0 cutoff →
    ‖(D.centeredMap K source calibration (fiveSectorFrame t positive small i).place z -
      D.centeredMap K source calibration (fiveSectorFrame t positive small i).place 0) - z‖ ≤
      ε * (z.re + z.im)
  traces : ∀ z ∈ {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff},
    value 0 = D.centeredMap K source calibration (fiveSectorFrame t positive small i).place 0 ∧
      ∀ h ∈ Set.Icc 0 (z.re + z.im),
        D.TraceVisibleAt K source calibration (fiveSectorFrame t positive small i).place value
          {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} (S.lower.point h) ∧
        D.TraceVisibleAt K source calibration (fiveSectorFrame t positive small i).place value
          {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} (S.upper.point h)

end Unfoldings.ConvexCap.RadialCutForest
