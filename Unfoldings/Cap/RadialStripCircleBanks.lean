module

public import Unfoldings.Cap.RadialStripCircleInterval
public import Unfoldings.Cap.RadialStripTraceVisibility
public import Unfoldings.Cap.StripCircleBanks

/-! Actual nonempty strip-circle slices retain their two distinct approached bank points. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}

/-- The strip construction discharges every geometric input. A nonempty circle slice
has distinct actual lower and upper bank values, even if either lies at a terminal pinch. -/
theorem circle_slice (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    {μ : ℝ} (small_error : ε < μ)
    (margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff)
    (meets : (data.value '' S.openSlab 0 cutoff ∩
      {z | ‖z - data.center‖ = radius}).Nonempty) :
    Nonempty (S.BankCircleSlice data.value data.center cutoff radius) := by
  have witness := meets
  obtain ⟨z, ⟨active, inside, _⟩, _⟩ := witness
  have member : active ∈ data.strictDomain := ⟨inside.1, inside.2.1.le, inside.2.2.le⟩
  exact (data.circle_interval small_error margin radius_positive far).exists_slice S
    data.continuous data.center cutoff radius radius_positive data.closed_injective
    (fun z member => data.strict_quadrant_of_margin small_error margin member)
    (fun z closed ends => data.end_levels_avoid_circle member radius_positive far closed ends)
    meets

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
