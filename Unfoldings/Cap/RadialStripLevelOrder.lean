module

public import Unfoldings.Cap.RadialStripPointOrder
public import Unfoldings.Geometry.FiniteAffineSegmentOrder
public import Unfoldings.Geometry.NearIdentityHeightOrder

/-! Actual strip traces preserve horizontal and reverse vertical order at each physical height. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}

/-- Individual coordinates, rather than only their signed difference, retain
the same-height order through arbitrary actual face-chart switches. -/
theorem same_height_order
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    (nonnegative : 0 ≤ ε) (small_error : ε ≤ 1 / 2)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement K calibration (fiveSectorFrame t positive small i).place f).linear z -
        z‖ ≤ ε * ‖z‖)
    {p q : ℂ} (first : p ∈ closure data.strictDomain) (last : q ∈ closure data.strictDomain)
    (horizontal : p.re ≤ q.re) (height : p.re + p.im = q.re + q.im) :
    (data.value p).re ≤ (data.value q).re ∧ (data.value q).im ≤ (data.value p).im := by
  let frame := (fiveSectorFrame t positive small i).place
  let A := fun f => (D.centeredCoordinatePlacement K source calibration frame f).toAffineMap
  have pb := data.closed_bounded first
  have qb := data.closed_bounded last
  have vertical : q.im ≤ p.im := by linarith
  have inside : segment ℝ p q ⊆ closure data.strictDomain := by
    intro z member
    obtain ⟨r, bounds, rfl⟩ := (segment_eq_image_lineMap ℝ p q).subset member
    let s : unitInterval := ⟨r, bounds⟩
    have bounded := S.segmentPath_mem_bounded
      (show p ∈ S.boundedCarrier 0 (q.re + q.im) from ⟨pb.1, pb.2.1, height.le⟩)
      (show q ∈ S.boundedCarrier 0 (q.re + q.im) from ⟨qb.1, qb.2.1, le_rfl⟩)
      horizontal vertical s
    exact data.closed_initial last bounded.1 bounded.2
  have steps (f : Face) : 0 ≤ ((A f).linear (q - p)).re ∧ ((A f).linear (q - p)).im ≤ 0 :=
    linear_near_identity_same_height_order (A f).linear nonnegative small_error
      (fun z => linear_error f z) horizontal height
  have progress (L : ℂ →L[ℝ] ℝ) (increments : ∀ f, 0 ≤ L ((A f).linear (q - p))) :
      L (data.value p) ≤ L (data.value q) := by
    apply finite_affine_selection_segment_order A
      (fun f => (A f).continuous_of_finiteDimensional) L data.continuous.continuousOn _ increments
    intro z member
    obtain ⟨f, _, _, value⟩ := data.visible_closure (inside member)
    exact ⟨f, value⟩
  have imaginary := progress (-Complex.imCLM) (fun f => neg_nonneg.mpr (steps f).2)
  change -(data.value p).im ≤ -(data.value q).im at imaginary
  exact ⟨progress Complex.reCLM (fun f => (steps f).1), neg_le_neg_iff.mp imaginary⟩

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
