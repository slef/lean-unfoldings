module

public import Unfoldings.Roof.CompatibleCutPartitionIndependence
public import Unfoldings.Geometry.SpatialEnvelopePartitionCopies

/-! All closed partial forest cuts retain the same original copies across partition changes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting.WholeCutModel

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  {R : K.CompatiblePotentialRouting U G boundary a β} {M : G.FiniteSlopeModel}
  (W V : R.WholeCutModel M)

local instance partialLeftCutPartitionFintype : Fintype W.Index := W.finiteIndex
local instance partialRightCutPartitionFintype : Fintype V.Index := V.finiteIndex

/-- Any closed portion of the actual forest cut has a partition-independent complete metric. -/
def partialCutModelEquiv (cuts : Set Plane) (closed : IsClosed cuts) (included : cuts ⊆ R.carrier) :
    W.partition.Cut cuts ≃ᵢ V.partition.Cut cuts :=
  W.partition.cutPartitionEquiv V.partition cuts closed
    (fun c => (W.carrier_disjoint_interior c).mono_right included)
    (fun c => (V.carrier_disjoint_interior c).mono_right included)

theorem restore_partialCutModelEquiv (cuts : Set Plane) (closed : IsClosed cuts)
    (included : cuts ⊆ R.carrier) (x : W.partition.Cut cuts) :
    V.partition.restoreCut cuts (W.partialCutModelEquiv V cuts closed included x) =
      W.partition.restoreCut cuts x :=
  W.partition.restoreCut_cutPartitionEquiv V.partition cuts closed
    (fun c => (W.carrier_disjoint_interior c).mono_right included)
    (fun c => (V.carrier_disjoint_interior c).mono_right included) x

/-- Processing another portion of the cuts commutes with changing the actual roof partition. -/
theorem partialCutModelEquiv_forgetCut (cuts other : Set Plane)
    (cuts_closed : IsClosed cuts) (other_closed : IsClosed other)
    (included : cuts ⊆ R.carrier) (restoring : other ⊆ cuts) (x : W.partition.Cut cuts) :
    V.partition.forgetCut cuts other restoring
      (W.partialCutModelEquiv V cuts cuts_closed included x) =
      W.partialCutModelEquiv V other other_closed (restoring.trans included)
        (W.partition.forgetCut cuts other restoring x) :=
  W.partition.cutPartitionEquiv_forgetCut V.partition cuts other restoring cuts_closed other_closed
    (fun c => (W.carrier_disjoint_interior c).mono_right included)
    (fun c => (V.carrier_disjoint_interior c).mono_right included) x

end Unfoldings.ConvexRoof.CompatiblePotentialRouting.WholeCutModel
