module

public import Unfoldings.Cap.RadialStripTraceData
public import Unfoldings.Cap.WaterfallBankControl

/-! Actual radial trace families supply all-face position control in their same calibration. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)
  {t : ℝ} (positive : 0 < t) (small : t < 1) (D : FacewiseDevelopment C N.retain)
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))

/-- Keep the actual subdivision's traces when applying the all-face estimates.
No second choice of calibration or development is needed. -/
theorem waterfallBankControl_of_radial_trace_data {ε cutoff : ℝ}
    (linear_error : ∀ (frame : Plane ≃ₗᵢ[ℝ] ℂ) f z,
      ‖(D.coordinatePlacement K
        (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) frame f).linear z - z‖ ≤
          ε * ‖z‖)
    (strips : ∀ i : FiveSector,
      ∃ P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
        ∀ S ∈ P.cells, Nonempty (N.RadialStripTraceData positive small D
          (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)) :
    N.WaterfallBankControl positive small D B ε cutoff := by
  refine ⟨linear_error, fun i => ?_⟩
  obtain ⟨P, cells⟩ := strips i
  refine ⟨P, fun S cell => ?_⟩
  obtain ⟨data⟩ := cells S cell
  exact ⟨data.value, data.continuous, data.equal, data.strict_injective,
    data.radial, data.bank_matching, data.source_error⟩

end Unfoldings.ConvexCap.RadialCutForest
