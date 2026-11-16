module

public import Unfoldings.Geometry.SpatialEnvelopeGraphTriangulation
public import Unfoldings.Roof.SpatialEnvelopeRoof
public import Unfoldings.Complex.RemovedSeamCarrier
public import Unfoldings.Metric.PolygonalCutCongr

/-! Actual finite roof meshes retain their original paired triangle metric and corner classes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane} {Z : ℝ}
  (T : Triangulation family Z)

local instance physicalCutMeshIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- The actual conforming mesh has an embedded spatial folding. -/
theorem pairedFolding_isEmbedded (conforming : TriangleFamily.Conforming T.projectedTriangle) :
    T.pairedFolding.IsEmbedded := by
  intro x y same
  exact T.pairedProjection_injective conforming (congrArg Cap.horizontal same)

/-- The two presentations use the same literal spatial triangles. -/
theorem graphPartition_cells_eq_faceImage :
    T.graphPartition.spatialCell = T.pairedFolding.faceImage :=
  funext T.graphPartition_spatialCell

/-- The graph-patch cut is the physical cut of the original paired triangles. -/
def graphPhysicalCutEquiv (cuts : Set Plane) :
    T.graphPartition.Cut cuts ≃ᵢ T.pairedFolding.PhysicalCut (Cap.horizontal ⁻¹' cuts) :=
  MetricGluing.polygonalCutCongr T.graphPartition.isClosed_spatialCell
    (fun i => (T.pairedFolding.compact_faceImage i).isClosed)
    T.graphPartition_cells_eq_faceImage (Cap.horizontal ⁻¹' cuts)

/-- Physical cut identification preserves the actual folded roof point. -/
theorem fold_graphPhysicalCutEquiv (cuts : Set Plane) (x : T.graphPartition.Cut cuts) :
    (T.pairedFolding.physicalCutSeams (Cap.horizontal ⁻¹' cuts)).fold
      (T.graphPhysicalCutEquiv cuts x) = T.graphPartition.fold cuts x :=
  MetricGluing.fold_polygonalCutCongr _ _ _ _ x

/-- A literal original face copy is preserved by the physical presentation change. -/
theorem graphPhysicalCutEquiv_faceMap (cuts : Set Plane) (f : T.Index)
    (x : T.pairedComplex.Cell f) :
    (T.graphPhysicalCutEquiv cuts).symm
      (T.pairedFolding.faceMapToPhysicalCut (Cap.horizontal ⁻¹' cuts) f x) =
        MetricGluing.of (fun f => T.graphPartition.spatialCell f)
          (MetricGluing.cutSeams T.graphPartition.spatialCell
            T.graphPartition.isClosed_spatialCell (Cap.horizontal ⁻¹' cuts)).relation f
          ⟨T.placement f x.val, Eq.mpr
            (congrArg (fun a : T.Index → Set Space => T.placement f x.val ∈ a f)
              T.graphPartition_cells_eq_faceImage) ⟨x.val, x.property, rfl⟩⟩ :=
  MetricGluing.polygonalCutCongr_symm_of _ _ _ _ f _

/-- Identify original retained pairings with the actual finite triangular graph-patch cut.
Only the geometric placement of removed and retained edges is assumed. -/
def pairedCutGraphEquiv (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (retain : Set T.pairedComplex.Seam) (cuts : Set Plane)
    (removed : ∀ s, s ∉ retain →
      ∀ x : (T.pairedComplex.triangle (T.pairedComplex.left s).face).Edge
        (T.pairedComplex.left s).edge,
        Cap.horizontal (T.placement (T.pairedComplex.left s).face x.val) ∈ cuts)
    (retained : ∀ s ∈ retain,
      Disjoint (T.pairedFolding.openSeamImage s) (Cap.horizontal ⁻¹' cuts)) :
    T.pairedComplex.Realization retain ≃ᵢ T.graphPartition.Cut cuts :=
  (T.pairedFolding.complexPhysicalCutEquiv (T.pairedFolding_isEmbedded conforming)
    retain (Cap.horizontal ⁻¹' cuts) removed retained).trans (T.graphPhysicalCutEquiv cuts).symm

/-- The original triangle-complex fold survives the complete metric identification. -/
theorem fold_pairedCutGraphEquiv
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (retain : Set T.pairedComplex.Seam) (cuts : Set Plane)
    (removed : ∀ s, s ∉ retain →
      ∀ x : (T.pairedComplex.triangle (T.pairedComplex.left s).face).Edge
        (T.pairedComplex.left s).edge,
        Cap.horizontal (T.placement (T.pairedComplex.left s).face x.val) ∈ cuts)
    (retained : ∀ s ∈ retain,
      Disjoint (T.pairedFolding.openSeamImage s) (Cap.horizontal ⁻¹' cuts))
    (x : T.pairedComplex.Realization retain) :
    T.graphPartition.fold cuts (T.pairedCutGraphEquiv conforming retain cuts removed retained x) =
      T.pairedFolding.toSpace retain x := by
  exact (MetricGluing.fold_polygonalCutCongr_symm _ _ _ _ _).trans
    (T.pairedFolding.fold_complexPhysicalCutEquiv (T.pairedFolding_isEmbedded conforming)
      retain (Cap.horizontal ⁻¹' cuts) removed retained x)

/-- The isometry preserves each original face tag and point, not just its spatial image. -/
theorem pairedCutGraphEquiv_faceMap
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (retain : Set T.pairedComplex.Seam) (cuts : Set Plane)
    (removed : ∀ s, s ∉ retain →
      ∀ x : (T.pairedComplex.triangle (T.pairedComplex.left s).face).Edge
        (T.pairedComplex.left s).edge,
        Cap.horizontal (T.placement (T.pairedComplex.left s).face x.val) ∈ cuts)
    (retained : ∀ s ∈ retain,
      Disjoint (T.pairedFolding.openSeamImage s) (Cap.horizontal ⁻¹' cuts))
    (f : T.Index) (x : T.pairedComplex.Cell f) :
    T.pairedCutGraphEquiv conforming retain cuts removed retained
      (T.pairedComplex.faceMap retain f x) =
        MetricGluing.of (fun f => T.graphPartition.spatialCell f)
          (MetricGluing.cutSeams T.graphPartition.spatialCell
            T.graphPartition.isClosed_spatialCell (Cap.horizontal ⁻¹' cuts)).relation f
          ⟨T.placement f x.val, Eq.mpr
            (congrArg (fun a : T.Index → Set Space => T.placement f x.val ∈ a f)
              T.graphPartition_cells_eq_faceImage) ⟨x.val, x.property, rfl⟩⟩ :=
  T.graphPhysicalCutEquiv_faceMap cuts f x

end Unfoldings.SpatialEnvelope.Triangulation
