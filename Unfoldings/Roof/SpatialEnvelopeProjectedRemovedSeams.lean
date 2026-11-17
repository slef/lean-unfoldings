module

public import Unfoldings.Roof.ProjectedRemovedSeams
public import Unfoldings.Geometry.SpatialEnvelopePhysicalCut

/-! Every intermediate retained mesh has its exact actual projected cut metric and face copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane} {Z : ℝ}
  (T : Triangulation family Z)

local instance projectedRemovedIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

variable (conforming : TriangleFamily.Conforming T.projectedTriangle)
  (inside : (interior (clip family Z)).Nonempty)

/-- Any chosen original retained-seam set gives exactly the graph patch cut along its
actual removed projected edges. Original metric copies are not identified by coincidence. -/
def projectedRemovedGraphEquiv (retain : Set T.pairedComplex.Seam) :
    T.pairedComplex.Realization retain ≃ᵢ
      T.graphPartition.Cut ((T.roof conforming inside).removedProjectedSeamCarrier retain) :=
  T.pairedCutGraphEquiv conforming retain _
    ((T.roof conforming inside).removed_edge_mem_projected_removed retain)
    ((T.roof conforming inside).openSeamImage_disjoint_projected_removed retain)

/-- The whole original folding is unchanged by the intermediate physical cut identification. -/
theorem fold_projectedRemovedGraphEquiv (retain : Set T.pairedComplex.Seam)
    (x : T.pairedComplex.Realization retain) :
    T.graphPartition.fold ((T.roof conforming inside).removedProjectedSeamCarrier retain)
      (T.projectedRemovedGraphEquiv conforming inside retain x) =
        T.pairedFolding.toSpace retain x :=
  T.fold_pairedCutGraphEquiv conforming retain _
    ((T.roof conforming inside).removed_edge_mem_projected_removed retain)
    ((T.roof conforming inside).openSeamImage_disjoint_projected_removed retain) x

/-- Each original face tag and point is preserved in the same literal physical cell. -/
theorem projectedRemovedGraphEquiv_faceMap (retain : Set T.pairedComplex.Seam)
    (f : T.Index) (x : T.pairedComplex.Cell f) :
    T.projectedRemovedGraphEquiv conforming inside retain (T.pairedComplex.faceMap retain f x) =
      MetricGluing.of (fun f => T.graphPartition.spatialCell f)
        (MetricGluing.cutSeams T.graphPartition.spatialCell T.graphPartition.isClosed_spatialCell
          (Cap.horizontal ⁻¹'
            (T.roof conforming inside).removedProjectedSeamCarrier retain)).relation f
        ⟨T.placement f x.val, Eq.mpr
          (congrArg (fun a : T.Index → Set Space => T.placement f x.val ∈ a f)
            T.graphPartition_cells_eq_faceImage) ⟨x.val, x.property, rfl⟩⟩ :=
  T.pairedCutGraphEquiv_faceMap conforming retain _
    ((T.roof conforming inside).removed_edge_mem_projected_removed retain)
    ((T.roof conforming inside).openSeamImage_disjoint_projected_removed retain) f x

end Unfoldings.SpatialEnvelope.Triangulation
