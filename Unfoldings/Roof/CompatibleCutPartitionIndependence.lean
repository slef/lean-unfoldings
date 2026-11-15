module

public import Unfoldings.Roof.CompatibleWholeCutModel
public import Unfoldings.Roof.CompatibleCutClosed
public import Unfoldings.Geometry.SpatialEnvelopePartitionIndependence

/-! The complete compatible forest cut metric is independent of the retained roof partition. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting.WholeCutModel

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  {R : K.CompatiblePotentialRouting U G boundary a β} {M : G.FiniteSlopeModel}
  (W V : R.WholeCutModel M)

local instance leftCutPartitionFintype : Fintype W.Index := W.finiteIndex
local instance rightCutPartitionFintype : Fintype V.Index := V.finiteIndex

/-- Every actual forest cut point avoids every original cell interior in the retained model. -/
theorem carrier_disjoint_interior (c : W.Index) :
    Disjoint (interior (W.partition.footprint c)) R.carrier := by
  apply Set.disjoint_left.mpr
  intro x inside on_cut
  obtain ⟨j, zero⟩ := R.carrier_covered_by_wholeCutEquations x on_cut
  have on_frontier := W.partition.mem_frontier_of_constraint R.wholeCutEquation
    R.wholeCutEquation_ne_zero W.signs W.aligned c (interior_subset inside) j zero
  exact on_frontier.2 inside

/-- Two actual retained models of the same whole forest cut have the same complete metric.
Boundary alignment, the common partition and all metric comparisons are derived. -/
def cutModelEquiv : W.Cut ≃ᵢ V.Cut :=
  W.partition.cutPartitionEquiv V.partition R.carrier R.isClosed_carrier
    W.carrier_disjoint_interior V.carrier_disjoint_interior

/-- The partition-independent metric identification retains the original physical roof point. -/
theorem restore_cutModelEquiv (x : W.Cut) :
    V.partition.restoreCut R.carrier (W.cutModelEquiv V x) = W.partition.restoreCut R.carrier x :=
  W.partition.restoreCut_cutPartitionEquiv V.partition R.carrier R.isClosed_carrier
    W.carrier_disjoint_interior V.carrier_disjoint_interior x

end Unfoldings.ConvexRoof.CompatiblePotentialRouting.WholeCutModel
