module

public import Unfoldings.Roof.CompatibleTerminalBanks
public import Unfoldings.Convex.ExteriorSpatialRays

/-! The constructed compatible terminal banks are complete closed embedded half-lines. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

/-- The same actual terminal bank witnesses are closed embedded dilations of a real half-line.
The cut, partition, both banks, exact physical folds and separation are all constructed. -/
theorem exists_whole_cut_partition_with_embedded_ray_banks (M : G.FiniteSlopeModel) :
    ∃ (A : Type) (_ : Fintype A) (P : SpatialEnvelope.WholePartition M.plane A),
      R.carrier ⊆ ⋃ a, frontier (P.footprint a) ∧ CompleteSpace (P.Cut R.carrier) ∧
      Function.Surjective (P.restoreCut R.carrier) ∧
      ∀ r : {v // v ∈ R.parents.roots}, ∃ T : ℝ, 0 < T ∧
        ∃ L B : Set.Ici T →ᵈ P.Cut R.carrier,
          (∀ t, (P.restoreCut R.carrier (L t)).val =
              SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex r) t.val) ∧
            (P.restoreCut R.carrier (B t)).val =
              SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex r) t.val)) ∧
          Topology.IsClosedEmbedding (L : Set.Ici T → P.Cut R.carrier) ∧
          Topology.IsClosedEmbedding (B : Set.Ici T → P.Cut R.carrier) ∧
          Disjoint (Set.range L) (Set.range B) := by
  obtain ⟨A, inst, P, boundary_cuts, complete, surjective, banks⟩ :=
    R.exists_whole_cut_partition_with_ray_banks M
  let : Fintype A := inst
  refine ⟨A, inst, P, boundary_cuts, complete, surjective, ?_⟩
  intro r
  obtain ⟨T, positive, L, B, folds, left_distances, right_distances, separated⟩ := banks r
  let : CompleteSpace (Set.Ici T) := isClosed_Ici.isComplete.completeSpace_coe
  let build (bank : Set.Ici T → P.Cut R.carrier)
      (distances : ∀ s t, edist (bank s) (bank t) =
        edist (SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex r) s.val))
          (SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex r) t.val))) :
      Set.Ici T →ᵈ P.Cut R.carrier := {
    toFun := bank
    edist_eq' := ⟨‖R.exterior.spatialDirection (R.terminalIndex r)‖₊,
      nnnorm_ne_zero_iff.mpr (R.exterior.spatialDirection_ne_zero (R.terminalIndex r)),
      fun s t => (distances s t).trans (R.exterior.edist_spatial_ray M (R.terminalIndex r)
        (positive.le.trans s.property) (positive.le.trans t.property))⟩ }
  let left := build L left_distances
  let right := build B right_distances
  exact ⟨T, positive, left, right, folds, Dilation.isClosedEmbedding left,
    Dilation.isClosedEmbedding right, separated⟩

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
