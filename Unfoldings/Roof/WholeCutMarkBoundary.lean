module

public import Unfoldings.Roof.CompatibleCutPartitionIndependence
public import Unfoldings.Geometry.SpatialEnvelopeRefinement

/-! Actual whole-roof cut marks have no interior planar-cell representatives. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting.WholeCutModel

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  {R : K.CompatiblePotentialRouting U G boundary a β} {M : G.FiniteSlopeModel}
  (W : R.WholeCutModel M)

local instance wholeCutMarkBoundaryFintype : Fintype W.Index := W.finiteIndex

/-- Every cell preimage of an actual physical forest-cut point is on that cell's boundary. -/
theorem cell_boundary_of_restore_mem (i : W.Index) (p : W.partition.planarCell i)
    (x : W.Cut)
    (named : MetricGluing.of (fun i => W.partition.planarCell i) (W.partition.cutGlue R.carrier)
      i p = x)
    (on_cut : Cap.horizontal (W.partition.restoreCut R.carrier x).val ∈ R.carrier) :
    p.val ∉ interior (W.partition.planarCell i) := by
  intro inside
  apply Set.disjoint_left.mp
    (SpatialEnvelope.WholePartition.Refinement.commonRegion_cut_disjoint_interior
      (P := W.partition) R.carrier W.carrier_disjoint_interior i)
    inside
  change Cap.horizontal ((M.plane (W.partition.support i)).place p.val) ∈ R.carrier
  have same := congrArg (fun z => Cap.horizontal (W.partition.restoreCut R.carrier z).val) named
  rw [W.partition.restoreCut_of] at same
  exact same.symm ▸ on_cut

end Unfoldings.ConvexRoof.CompatiblePotentialRouting.WholeCutModel
