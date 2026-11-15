module

public import Unfoldings.Cap.RimStartedContour
public import Unfoldings.Cap.ProjectedContourSides
public import Unfoldings.Development.FlatDisk

/-! Rim-started cut contours with every original bank positively oriented in projection. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)

include K roots in
/-- Rim starting position and the physical orientation of every original face are derived.
The development used to propagate orientation belongs only to the final flat cut disk;
no development of an intermediate surface with fresh curvature is used. -/
theorem exists_positive_rim_contour :
    ∃ Q : C.BoundaryContour (C.selectedRetain S),
      C.contourOriginalVertex S Q 0 ∈ P.roots ∧
        ∀ i : Fin (Q.length + 1), 0 < K.projectedGermOrientation (Q.cycle.point i).val := by
  let retain := C.selectedRetain S
  let disk := C.selectedCutDisk S roots K.folding K.diskHomeomorph
  let : ConnectedSpace (Metric.closedBall (0 : Plane) 1) :=
    isConnected_iff_connectedSpace.mp
      ((convex_closedBall (0 : Plane) 1).isConnected ⟨0, Metric.mem_closedBall_self zero_le_one⟩)
  let : ConnectedSpace (C.Realization retain) :=
    disk.symm.surjective.connectedSpace disk.symm.continuous
  have connected := C.duallyConnected_of_preconnected retain
  have flat (w : C.Vertex retain) (internal : ¬ C.IsBoundaryVertex retain w) :
      C.totalAngle retain w = 2 * Real.pi :=
    (internal (C.selectedCut_all_vertices_boundary S roots w)).elim
  obtain ⟨D, _local⟩ := K.folding.exists_locally_isometric_development_of_flat_disk retain disk flat
  obtain ⟨Q, positive⟩ := K.exists_projection_positive_contour retain
    (K.folding.boundaryGraph_connected_of_disk retain disk)
  have all_positive (i : Fin (Q.length + 1)) :
      0 < K.projectedGermOrientation (Q.cycle.point i).val :=
    D.projectedGermOrientation_cycle_positive K connected Q.cycle positive i
  obtain ⟨root⟩ := (K.folding.boundaryGraph_connected_of_disk Set.univ K.diskHomeomorph).nonempty
  have marked : root.val ∈ P.roots := roots.symm ▸ root.property
  obtain ⟨index, first⟩ := List.mem_ofFn.mp (C.mem_selectedContourSeeds S roots Q root.val)
  refine ⟨Q.rotate C index, ?_, ?_⟩
  · have at_root : C.contourOriginalVertex S (Q.rotate C index) 0 = root.val := by
      change C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex _ ((Q.rotate C index).cycle.first)) = root.val
      rw [TriangleComplex.BoundaryContour.rotate_first]
      exact first
    exact at_root.symm ▸ marked
  · intro i
    exact all_positive (finCycle index i)

/-- A physically positive original contour, started on the original rim. -/
def positiveRimContour : C.BoundaryContour (C.selectedRetain S) :=
  (K.exists_positive_rim_contour S roots).choose

theorem positiveRimContour_starts :
    C.contourOriginalVertex S (K.positiveRimContour S roots) 0 ∈ P.roots :=
  (K.exists_positive_rim_contour S roots).choose_spec.1

theorem positiveRimContour_positive (i : Fin ((K.positiveRimContour S roots).length + 1)) :
    0 < K.projectedGermOrientation ((K.positiveRimContour S roots).cycle.point i).val :=
  (K.exists_positive_rim_contour S roots).choose_spec.2 i

end Unfoldings.ConvexCap
