module

public import Unfoldings.Roof.AffineFloorRoof
public import Unfoldings.Complex.PhysicalCutEquiv
public import Unfoldings.Geometry.SpatialEnvelopeOpenSeams
public import Unfoldings.Metric.PolygonalCutCongr

/-! The affine-floor triangle complex is the actual cut of its physical graph patch. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.FloorMesh

universe u

variable {I J : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {floor : Plane →ᵃ[ℝ] ℝ} {extra : J → Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  (T : FloorMesh family floor extra Z)

local instance floorPhysicalCutIndexFinite : Finite T.Index := T.finite
local instance floorPhysicalCutIndexFintype : Fintype T.Index := Fintype.ofFinite _

/-- Both presentations use literally the same triangles in the original support planes. -/
theorem graphPartition_cells_eq_faceImage : T.graphPartition.spatialCell = T.pairedFolding.faceImage := by
  funext i
  change T.placement i '' ((family (T.support i)).project.symm '' (T.projectedTriangle i).carrier) =
    T.placement i '' (T.triangle i).carrier
  rw [T.triangle_carrier]

theorem pairedFolding_isEmbedded : T.pairedFolding.IsEmbedded :=
  fun _ _ equal => T.pairedProjection_injective (congrArg Cap.horizontal equal)

/-- Re-express the same physical patch in its paired triangles. -/
def graphPhysicalCutEquiv (cuts : Set Plane) :
    T.graphPartition.Cut cuts ≃ᵢ T.pairedFolding.PhysicalCut (Cap.horizontal ⁻¹' cuts) :=
  MetricGluing.polygonalCutCongr T.graphPartition.isClosed_spatialCell
    (fun i => (T.pairedFolding.compact_faceImage i).isClosed)
    T.graphPartition_cells_eq_faceImage (Cap.horizontal ⁻¹' cuts)

variable (retain : Set T.pairedComplex.Seam) (cuts : Set Plane)
  (removed : ∀ s, s ∉ retain →
    ∀ x : (T.pairedComplex.triangle (T.pairedComplex.left s).face).Edge
      (T.pairedComplex.left s).edge,
      Cap.horizontal (T.placement (T.pairedComplex.left s).face x.val) ∈ cuts)
  (retained : ∀ s ∈ retain,
    Disjoint (T.pairedFolding.openSeamImage s) (Cap.horizontal ⁻¹' cuts))

/-- The finite triangle cut retains exactly its intended physical seams. -/
def pairedCutGraphEquiv : T.pairedComplex.Realization retain ≃ᵢ T.graphPartition.Cut cuts :=
  (T.pairedFolding.complexPhysicalCutEquiv T.pairedFolding_isEmbedded
    retain (Cap.horizontal ⁻¹' cuts) removed retained).trans (T.graphPhysicalCutEquiv cuts).symm

/-- The finite metric identification preserves each original spatial point. -/
theorem fold_pairedCutGraphEquiv (x : T.pairedComplex.Realization retain) :
    T.graphPartition.fold cuts (T.pairedCutGraphEquiv retain cuts removed retained x) =
      T.pairedFolding.toSpace retain x :=
  (MetricGluing.fold_polygonalCutCongr_symm _ _ _ _ _).trans
    (T.pairedFolding.fold_complexPhysicalCutEquiv T.pairedFolding_isEmbedded
      retain (Cap.horizontal ⁻¹' cuts) removed retained x)

/-- The actual open seam projects onto its original open projected edge. -/
theorem horizontal_openSeamImage (s : T.pairedComplex.Seam) :
    Cap.horizontal '' T.pairedFolding.openSeamImage s =
      openSegment ℝ
        ((T.projectedTriangle (T.pairedComplex.left s).face).vertex (T.pairedComplex.left s).edge)
        ((T.projectedTriangle (T.pairedComplex.left s).face).vertex
          (Triangle.next (T.pairedComplex.left s).edge)) := by
  change Cap.horizontal '' openSegment ℝ
    ((T.pairedFolding.place (T.pairedComplex.left s).face)
      ((T.pairedComplex.triangle (T.pairedComplex.left s).face).vertex
        (T.pairedComplex.left s).edge))
    ((T.pairedFolding.place (T.pairedComplex.left s).face)
      ((T.pairedComplex.triangle (T.pairedComplex.left s).face).vertex
        (Triangle.next (T.pairedComplex.left s).edge))) = _
  refine (image_openSegment ℝ Cap.horizontal.toAffineMap _ _).trans ?_
  congr 1 <;>
    exact ((family (T.support (T.pairedComplex.left s).face)).horizontal_place _).trans
      ((family (T.support (T.pairedComplex.left s).face)).project.apply_symm_apply _)

/-- Closed original edges omitted by `retainOutside` lie in the actual physical cut. -/
theorem removed_edge_mem_cut (cuts : Set Plane) (s : T.pairedComplex.Seam)
    (removed : s ∉ T.retainOutside cuts)
    (x : (T.pairedComplex.triangle (T.pairedComplex.left s).face).Edge
      (T.pairedComplex.left s).edge) :
    Cap.horizontal (T.placement (T.pairedComplex.left s).face x.val) ∈ cuts := by
  have selected : (T.projectedTriangle (T.pairedComplex.left s).face).edge
      (T.pairedComplex.left s).edge ⊆ cuts := not_not.mp removed
  exact selected (by
    change Cap.horizontal ((family (T.support (T.pairedComplex.left s).face)).place x.val) ∈ _
    rw [(family (T.support (T.pairedComplex.left s).face)).horizontal_place]
    exact (T.edgeProjection (T.pairedComplex.left s).face (T.pairedComplex.left s).edge x).property)

/-- If touching a cut at a nonvertex edge point forces the whole edge into the cut,
then every retained open physical seam avoids it. This is a geometric condition only. -/
theorem retained_openSeamImage_disjoint (cuts : Set Plane)
    (aligned : ∀ f e (x : (T.projectedTriangle f).Edge e),
      ¬ (T.projectedTriangle f).IsVertex x.val → x.val ∈ cuts →
        (T.projectedTriangle f).edge e ⊆ cuts)
    (s : T.pairedComplex.Seam) (kept : s ∈ T.retainOutside cuts) :
    Disjoint (T.pairedFolding.openSeamImage s) (Cap.horizontal ⁻¹' cuts) := by
  apply Set.disjoint_left.mpr
  intro z inside member
  have projected := (T.horizontal_openSeamImage s).subset ⟨z, inside, rfl⟩
  exact kept (aligned (T.pairedComplex.left s).face (T.pairedComplex.left s).edge
    ⟨Cap.horizontal z, openSegment_subset_segment ℝ _ _ projected⟩
    ((T.projectedTriangle (T.pairedComplex.left s).face).not_isVertex_of_mem_openSegment
      (T.pairedComplex.left s).edge projected) member)

end Unfoldings.SpatialEnvelope.FloorMesh
