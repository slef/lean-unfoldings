module

public import Unfoldings.Cap.EmptyCircleTerminalCopy
public import Unfoldings.Cap.ProperComparisonData

/-! Ordered proper comparison arcs continue a disappearing strip's actual terminal copy. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))
  (i : FiveSector) {S : MonotoneStrip} {ε cutoff : ℝ}
  (data : N.RadialStripTraceData positive small D
    (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)

/-- These arcs start at this strip's own approached copy. Their simplicity and
circle order are proved; separation from other strips is a further theorem. -/
structure EmptyCircleContinuation (physicalRadius radius : ℝ) where
  height : ℝ
  height_bounds : height ∈ Set.Ioo (0 : ℝ) cutoff
  merged : ∀ k ∈ Set.Icc height cutoff, S.lower.coordinate k = S.upper.coordinate k
  lower_closed : S.lower.point height ∈ closure (S.openSlab 0 cutoff)
  upper_closed : S.upper.point height ∈ closure (S.openSlab 0 cutoff)
  inside : ‖data.value (S.lower.point height) - data.center‖ < radius
  vertex : C.Vertex Set.univ
  on_cuts : K.projectedVertex vertex ∈ cuts
  physical : source + (fiveSectorFrame t positive small i).place.symm (S.lower.point height) =
    K.projectedVertex vertex
  physical_inside : ‖K.projectedVertex vertex - source‖ < physicalRadius
  target : Fin (N.completedContour.length + 1)
  original : C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = vertex
  value : data.value (S.lower.point height) = B.sectorFrame i
    ((N.completedDevelopment D).boundaryPosition (N.completedContour.cycle.point target))
  comparison : B.ProperComparisonData vertex target (D.projectedMap K source) physicalRadius radius

/-- An actual terminal trace lies far enough inside the physical stopping ball
to apply the already proved comparison construction in this same calibration. -/
theorem exists_emptyCircleContinuation
    (pinches : S.ApproachedPinchesIn
      (Set.range (fun w : {w : C.Vertex Set.univ // K.projectedVertex w ∈ cuts} =>
        (fiveSectorFrame t positive small i).place (K.projectedVertex w.val - source))) 0 cutoff)
    (small_error : ε < 1 / 2) {physicalRadius radius : ℝ}
    (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
    (physical_far : radius < (1 / 2 - ε) * physicalRadius)
    (outside : radius ∉ data.emptyCircleExceptions)
    (empty : data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius} = ∅)
    (nonempty : (S.openSlab 0 cutoff).Nonempty)
    (construct : ∀ w : C.Vertex Set.univ, K.projectedVertex w ∈ cuts →
      ‖K.projectedVertex w - source‖ < physicalRadius →
      ∀ target : Fin (N.completedContour.length + 1),
        C.vertexForgetCuts (Set.subset_univ _)
          (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = w →
        ‖(N.completedDevelopment D).boundaryPosition (N.completedContour.cycle.point target) -
          D.projectedMap K source‖ < radius →
        Nonempty (B.ProperComparisonData w target
          (D.projectedMap K source) physicalRadius radius)) :
    Nonempty (B.EmptyCircleContinuation i data physicalRadius radius) := by
  obtain ⟨h, bounds, merged, first, last, near, w, on_cut, physical, target, original, value⟩ :=
    B.exists_terminal_copy_of_empty_circle i data pinches radius_positive far outside empty nonempty
  have horizontal : 0 ≤ (S.lower.point h).re := by
    have bound := S.lower.coordinate_mono bounds.1.le
    rwa [data.lower_source] at bound
  have vertical : 0 ≤ (S.lower.point h).im := by
    have bound := S.lower.complement_mono bounds.1.le
    change 0 - S.lower.coordinate 0 ≤ h - S.lower.coordinate h at bound
    change 0 ≤ h - S.lower.coordinate h
    simpa only [data.lower_source, sub_self] using bound
  have norm_bound : ‖S.lower.point h‖ ≤ h := by
    have bound := Complex.norm_le_abs_re_add_abs_im (S.lower.point h)
    rwa [abs_of_nonneg horizontal, abs_of_nonneg vertical, S.lower.point_height] at bound
  have included : S.openSlab 0 cutoff ⊆ data.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have closed := closure_mono included first
  have distance := data.closed_distance_lower closed
  rw [S.lower.point_height] at distance
  have height_bound : h < physicalRadius := by nlinarith
  have physical_inside : ‖K.projectedVertex w - source‖ < physicalRadius := by
    rw [← physical, add_sub_cancel_left, LinearIsometryEquiv.norm_map]
    exact norm_bound.trans_lt height_bound
  have center : data.center = B.sectorFrame i (D.projectedMap K source) := by
    change D.centeredMap K source _ _ 0 = _
    simp only [FacewiseDevelopment.centeredMap, map_zero, add_zero]
    rfl
  have developed_inside : ‖(N.completedDevelopment D).boundaryPosition
      (N.completedContour.cycle.point target) - D.projectedMap K source‖ < radius := by
    rw [value, center, ← map_sub, (B.sectorFrame i).norm_map] at near
    exact near
  obtain ⟨comparison⟩ := construct w on_cut physical_inside target original developed_inside
  exact ⟨{
    height := h
    height_bounds := bounds
    merged := merged
    lower_closed := first
    upper_closed := last
    inside := near
    vertex := w
    on_cuts := on_cut
    physical := physical
    physical_inside := physical_inside
    target := target
    original := original
    value := value
    comparison := comparison }⟩

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
