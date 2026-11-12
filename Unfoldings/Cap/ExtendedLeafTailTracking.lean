module

public import Unfoldings.Cap.LeafCompletedTailTracking
public import Unfoldings.Cap.ExtendedLeafCoherence

/-! Construct actual fine parent-edge representations of every geometric leaf-tail point. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ}

/-- The fine outward forest, geometric leaf, and deep roof alone determine an
actual parent-path point at every tail height. No matching certificate, containing
edge, developed map, or acuteness of the auxiliary triangulation is supplied. -/
theorem cornerExtendedOutward_leaf_tail_on_parent_path (positive : 0 < t) (small : t < 1)
    (T : K.ClipSpatialTriangles Z) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0)
    (cutoff : ℝ)
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z)) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    let covered := T.cornerTails_covers_rim inside source_height lower
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    let R := (M.cornerExtendedOutwardForest positive small T
      internal source_height lower).val
    ∀ i : FiveSector, ∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
      ∃ w : L.partition.pairedComplex.Vertex Set.univ,
        Q.projectedVertex w = F.geometricPosition leaf.val ∧
        ∀ h ∈ Set.Icc (leaf.point.re + leaf.point.im) cutoff,
          ∃ j : Fin (R.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
            K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm
              (leaf.tailGraph.graph.point h) = (R.completedRootPath w).point j s := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let covered := T.cornerTails_covers_rim inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let network := M.cornerExtendedOutwardForest positive small T internal source_height lower
  let R := network.val
  refine fun i leaf => ?_
  obtain ⟨w, at_vertex, _⟩ := M.meshed_geometric_nonroot_vertex F covered positive small lower
    T leaf.val leaf.property.1
  refine ⟨w, at_vertex, fun h member => ?_⟩
  obtain ⟨j, s, value⟩ := leaf.tailGraph_point_on_completed_path R network.property w at_vertex
    (L.partition.normalizedCap_footprint L.conforming lower) deep member
  refine ⟨j, s, ?_⟩
  rw [value, LinearIsometryEquiv.symm_apply_apply]
  abel

end Unfoldings.ConvexCap.SectorForest
