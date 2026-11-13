module

public import Unfoldings.Roof.TailHeightBankGeometry
public import Unfoldings.Cap.EmptyCircleContinuation
public import Unfoldings.Cap.RadialStripPhysicalMap
public import Unfoldings.Cap.CompletedProperComparisonData
public import Unfoldings.Cap.SectorSweepBall
public import Unfoldings.Geometry.StripInsertionTerminalTail

/-! A disappearing strip's own terminal copy has proper comparison arcs in that strip's sector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {outerDomain : Set Plane} {F : K.SkirtTailFamily outerDomain (origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {i : FiveSector}

theorem terminal_geometric_tail
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {S : MonotoneStrip} {ε cutoff physicalRadius circle : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (tails : S.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    (continuation : B.EmptyCircleContinuation i data physicalRadius circle) :
    ∃ leaf : M.GeometricSectorLeaf F covered positive small i,
      leaf.point.re + leaf.point.im ≤ continuation.height ∧
      (fiveSectorFrame t positive small i).place
        (Q.projectedVertex continuation.vertex - origin) =
          leaf.tailGraph.graph.point continuation.height ∧
      ∀ k ∈ Set.Icc continuation.height cutoff,
        S.lower.point k = leaf.tailGraph.graph.point k ∧
          S.upper.point k = leaf.tailGraph.graph.point k := by
  let frame := (fiveSectorFrame t positive small i).place
  obtain ⟨leaf, after_leaf, follows⟩ := tails continuation.height continuation.height_bounds
    continuation.merged
  have points (k : ℝ) (within : k ∈ Set.Icc continuation.height cutoff) :
      S.lower.point k = leaf.tailGraph.graph.point k ∧
        S.upper.point k = leaf.tailGraph.graph.point k :=
    ⟨S.lower.point_eq_of_same_coordinate leaf.tailGraph.graph (follows k within).1,
      S.upper.point_eq_of_same_coordinate leaf.tailGraph.graph (follows k within).2⟩
  refine ⟨leaf, after_leaf, ?_, points⟩
  rw [← continuation.physical, add_sub_cancel_left, frame.apply_symm_apply]
  exact (points continuation.height ⟨le_rfl, continuation.height_bounds.2.le⟩).1

/-- Both permanently merged physical banks are tracked by the same actual fine
parent path starting at this terminal vertex. -/
theorem terminal_banks_on_completed_path
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {S : MonotoneStrip} {ε cutoff physicalRadius circle : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (tails : S.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    (continuation : B.EmptyCircleContinuation i data physicalRadius circle)
    (footprint : Q.footprint = outerDomain)
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain)) :
    ∀ k ∈ Set.Icc continuation.height cutoff,
      ∃ j : Fin (R.spanningCompletion.parents.distanceToRoot continuation.vertex),
        ∃ s : unitInterval,
        origin + (fiveSectorFrame t positive small i).place.symm
          (S.lower.point k) = (R.completedRootPath continuation.vertex).point j s ∧
        origin + (fiveSectorFrame t positive small i).place.symm
          (S.upper.point k) = (R.completedRootPath continuation.vertex).point j s := by
  obtain ⟨leaf, after_leaf, same_start, follows⟩ :=
    terminal_geometric_tail R D B data tails continuation
  intro k within
  obtain ⟨j, s, at_point⟩ := leaf.tailGraph_point_on_completed_path_from_height R outward
    continuation.vertex after_leaf same_start footprint deep within
  refine ⟨j, s, ?_, ?_⟩
  · rw [(follows k within).1, at_point, LinearIsometryEquiv.symm_apply_apply]
    abel
  · rw [(follows k within).2, at_point, LinearIsometryEquiv.symm_apply_apply]
    abel

/-- Retarget the actual parent path at this strip's terminal fine vertex.
Its own contour copy is retained and every sector hypothesis is derived from
the named physical tail. No global separation from other strips is asserted. -/
theorem empty_circle_comparison_in_sector
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {S : MonotoneStrip} {ε cutoff μ physicalRadius circle : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (tails : S.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    (continuation : B.EmptyCircleContinuation i data physicalRadius circle)
    (footprint : Q.footprint = outerDomain)
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    (room : 2 * physicalRadius < cutoff) (nonnegative : 0 ≤ μ)
    (face_bounds : ∀ (j : FiveSector) f p, p ∈ (Q.projectedTriangle f).carrier →
      p - origin ∈ closedFiveSector t j →
      p ∈ sectorSweepInterior positive small (origin) cutoff →
      μ * ‖p - origin‖ ≤
        (B.sectorFrame j (D.projectedPlacement Q f p -
          D.projectedMap Q (origin))).re ∧
      μ * ‖p - origin‖ ≤
        (B.sectorFrame j (D.projectedPlacement Q f p -
          D.projectedMap Q (origin))).im)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (budget : FineC.totalInteriorAngularDefect Set.univ < Real.pi)
    (far : circle < μ * physicalRadius) :
    ∃ comparison : B.ProperComparisonData continuation.vertex continuation.target
      (D.projectedMap Q (origin)) physicalRadius circle,
      comparison.sector = i := by
  let source := origin
  obtain ⟨leaf, after_leaf, same_start, _⟩ :=
    terminal_geometric_tail R D B data tails continuation
  have before_end := continuation.height_bounds.2.trans (leaf.tail_end_beyond_clip_ball deep)
  obtain ⟨positions, directions, sectors⟩ := leaf.completed_bank_geometry_from_height R outward
    continuation.vertex after_leaf before_end same_start curvature_covered
  have radius_positive : 0 < physicalRadius :=
    (norm_nonneg _).trans_lt continuation.physical_inside
  have radius_cutoff : physicalRadius ≤ cutoff := by linarith
  have deepQ : Metric.closedBall source physicalRadius ⊆ interior Q.footprint := by
    rw [footprint]
    exact (Metric.closedBall_subset_closedBall radius_cutoff).trans deep
  have bounded_faces (f) (p : Plane) (member : p ∈ (Q.projectedTriangle f).carrier)
      (bounded : ‖p - source‖ ≤ physicalRadius) (cone : p - source ∈ closedFiveSector t i) :=
    face_bounds i f p member cone (closedBall_subset_sectorSweepInterior positive small source room
      (by rw [Metric.mem_closedBall, dist_eq_norm]; exact bounded))
  have actual_inside : ‖(R.completedDevelopment D).boundaryPosition
      (R.completedContour.cycle.point continuation.target) - D.projectedMap Q source‖ < circle := by
    have near := continuation.inside
    rw [continuation.value] at near
    change ‖data.outputFrame ((R.completedDevelopment D).boundaryPosition
      (R.completedContour.cycle.point continuation.target)) - data.center‖ < circle at near
    rw [data.center_eq_outputFrame, ← data.outputFrame.map_sub, data.outputFrame.norm_map] at near
    exact near
  exact B.exists_proper_comparison_data_in_sector i outward continuation.vertex
    continuation.on_cuts (D.projectedMap Q source) μ physicalRadius nonnegative
    continuation.physical_inside deepQ positions directions sectors bounded_faces budget
    continuation.target continuation.original circle actual_inside far

end Unfoldings.ConvexRoof.SectorForest
