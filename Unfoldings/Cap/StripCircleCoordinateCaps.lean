module

public import Unfoldings.Geometry.CircleCoordinateCaps
public import Unfoldings.Cap.CrossFrameStripCircleBounds

/-! Actual strip-circle images lie in the portions bounded by their named bank coordinates. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))
  (i : FiveSector) {S : MonotoneStrip} {ε cutoff radius : ℝ}
  (data : N.RadialStripTraceData positive small D
    (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
  (slice : S.BankCircleSlice data.value data.center cutoff radius)
  (ordered : (data.value (S.lower.point slice.lowerHeight) - data.center).re <
    (data.value (S.upper.point slice.upperHeight) - data.center).re)
  {μ : ℝ} (small_error : ε < μ)
  (margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
    μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
  (radius_positive : 0 < radius)

include ordered small_error margin radius_positive

theorem circle_image_subset_upper_cap :
    data.outputFrame.symm '' (data.value '' S.openSlab 0 cutoff ∩
        {z | ‖z - data.center‖ = radius}) ⊆
      circleUpperCap (B.sectorFrame i) (D.projectedMap K source) radius
        (data.value (S.upper.point slice.upperHeight) - data.center).re := by
  intro p member
  have bounds := B.circle_image_open_bank_bounds i data slice ordered small_error margin
    radius_positive member
  exact ⟨bounds.1.le, bounds.2.1, bounds.2.2.1, bounds.2.2.2.2⟩

theorem circle_image_subset_lower_cap :
    data.outputFrame.symm '' (data.value '' S.openSlab 0 cutoff ∩
        {z | ‖z - data.center‖ = radius}) ⊆
      circleLowerCap (B.sectorFrame i) (D.projectedMap K source) radius
        (data.value (S.lower.point slice.lowerHeight) - data.center).im := by
  intro p member
  have bounds := B.circle_image_open_bank_bounds i data slice ordered small_error margin
    radius_positive member
  exact ⟨bounds.1.le, bounds.2.1, bounds.2.2.2.1, bounds.2.2.2.2⟩

omit ordered small_error margin radius_positive in
theorem circle_caps_disjoint_of_common_point (j : FiveSector) (actual : Plane)
    (first_quadrant : 0 < (B.sectorFrame i (actual - D.projectedMap K source)).re ∧
      0 < (B.sectorFrame i (actual - D.projectedMap K source)).im)
    (last_quadrant : 0 < (B.sectorFrame j (actual - D.projectedMap K source)).re ∧
      0 < (B.sectorFrame j (actual - D.projectedMap K source)).im)
    (inside : ‖actual - D.projectedMap K source‖ ≤ radius) :
    Disjoint (circleUpperCap (B.sectorFrame i) (D.projectedMap K source) radius
        (B.sectorFrame i (actual - D.projectedMap K source)).re)
      (circleLowerCap (B.sectorFrame j) (D.projectedMap K source) radius
        (B.sectorFrame j (actual - D.projectedMap K source)).im) := by
  apply Set.disjoint_left.mpr
  intro p first last
  exact B.inner_barrier_point_exclusion_of_norm_le i j (D.projectedMap K source) actual p
    first_quadrant last_quadrant ⟨first.1, first.2.1⟩ ⟨last.1, last.2.1⟩ first.2.2.1 last.2.2.1
    (inside.trans_eq first.2.2.2.symm)

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
