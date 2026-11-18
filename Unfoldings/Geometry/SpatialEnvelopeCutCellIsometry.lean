module

public import Unfoldings.Geometry.SpatialEnvelopeCut
public import Unfoldings.Metric.IsometricCells

/-! Every original whole-roof cell embeds isometrically and closedly in each physical cut. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A] (cuts : Set Plane)

/-- Original spatial placement rules out all metric shortcuts inside an actual roof cell. -/
theorem cut_cell_isometry (i : A) :
    Isometry (MetricGluing.of (fun i => P.planarCell i) (P.cutGlue cuts) i) := by
  apply MetricGluing.of_isometry_of_compatible (fun i => P.planarCell i) (P.cutGlue cuts)
    (fun i p => (family (P.support i)).place p.val)
  · intro i x y
    exact (family (P.support i)).place.isometry x.val y.val
  · intro x y joined
    exact ((P.glue_iff x y).mp (P.cutGlue_subset cuts x y joined)).2

/-- Each original closed cell remains closed in the actual intrinsic cut metric. -/
theorem cut_cell_isClosedEmbedding (i : A) :
    Topology.IsClosedEmbedding (MetricGluing.of (fun i => P.planarCell i) (P.cutGlue cuts) i) := by
  let : CompleteSpace (P.planarCell i) := (P.isClosed_planarCell i).isComplete.completeSpace_coe
  exact (P.cut_cell_isometry cuts i).isClosedEmbedding

end Unfoldings.SpatialEnvelope.WholePartition
