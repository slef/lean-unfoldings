module

public import Unfoldings.Roof.CompletionBankVertexParameters
public import Unfoldings.Roof.MarkedContourPartition
public import Unfoldings.Roof.CompletionCombinedConstraints
public import Unfoldings.Geometry.ChainEndTrimming

/-! Marked trim endpoints select actual fine original-bank indices in their true order. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ}

local instance markedOriginalWindowIndexFintype {region : Set Plane} {J : Type u}
    {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra) :
    Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

open Classical in
/-- Each prescribed closing corner is an actual vertex of this very physical cap. -/
theorem exists_markedClosure_vertex {n : ℕ} (P : PolygonalChain Plane n) (q c : Plane)
    (jordan : Schoenflies.IsJordanCurve (P.threeSegmentClosure q c))
    (E : K.CompletionMesh φ (PlanarTopology.closedJordanDomain (P.threeSegmentClosure q c))
      (P.markedClosureEquations q c)) (j : Fin 4) :
    ∃ v : E.mesh.pairedComplex.Vertex Set.univ,
      E.cap.projectedVertex v = P.closureMarkedPoint q c j := by
  have in_filling : P.closureMarkedPoint q c j ∈
      PlanarTopology.closedJordanDomain (P.threeSegmentClosure q c) := by
    have on_curve := P.closureMarkedPoint_mem_curve q c j
    rw [← PlanarTopology.frontier_closedJordanDomain jordan] at on_curve
    exact (closure_eq_iff_isClosed.mpr isClosed_closure).subset
      (frontier_subset_closure on_curve)
  exact E.exists_projected_vertex_of_coordinate_constraints (P.closureMarkedPoint q c j)
    (fun k => ULift.up (.inr (j, k))) (fun _ => rfl) in_filling

variable {retain : Set C.Seam} {n : ℕ}
  (coarse : (C.boundarySystem retain).Chain (n + 1))
  (cut : ∀ i, ¬ C.IsBoundaryEdge Set.univ (C.germEdge (coarse.point i).val))
  (a b : unitInterval) (q c : Plane)

local notation "P" => SpatialFolding.projectedBoundaryChain K.folding coarse
local notation "Q" => PolygonalChain.trimEnds
  (SpatialFolding.projectedBoundaryChain K.folding coarse) a b

open Classical in
/-- Marked geometric trims produce actual fine-bank starting indices, in the exact
original order. No endpoint-copy index or fine vertex occurrence is supplied. -/
theorem exists_trimmed_original_bank_indices (first_before : a.val < 1)
    (last_before : b.val < 1)
    (jordan : Schoenflies.IsJordanCurve ((Q).threeSegmentClosure q c))
    (E : K.CompletionMesh φ (PlanarTopology.closedJordanDomain ((Q).threeSegmentClosure q c))
      (K.combinedCompletionEquations ((Q).markedClosureEquations q c))) :
    let fine := E.originalConstraintView.originalChainRefinement retain coarse cut
    ∃ first : Fin ((fine.block 0).length + 1),
      ∃ last : Fin ((fine.block (Fin.last (n + 1))).length + 1),
        fine.blockParameter 0 first.castSucc = a ∧
        fine.blockParameter (Fin.last (n + 1)) last.castSucc = b ∧
        fine.blockIndex 0 first < fine.blockIndex (Fin.last (n + 1)) last := by
  dsimp only
  let fine := E.originalConstraintView.originalChainRefinement retain coarse cut
  obtain ⟨v, at_start⟩ := E.extraConstraintView.exists_markedClosure_vertex (Q) q c jordan 0
  have at_start' : (P).point 0 a = E.originalConstraintView.cap.projectedVertex v :=
    ((P).trimEnds_start a b).symm.trans at_start.symm
  obtain ⟨first, first_time⟩ := fine.exists_block_start_parameter_of_cap_vertex 0 a first_before
    v at_start'
  obtain ⟨w, at_end⟩ := E.extraConstraintView.exists_markedClosure_vertex (Q) q c jordan 1
  have at_end' : (P).point (Fin.last (n + 1)) b =
      E.originalConstraintView.cap.projectedVertex w :=
    ((P).trimEnds_last a b).symm.trans at_end.symm
  obtain ⟨last, last_time⟩ := fine.exists_block_start_parameter_of_cap_vertex
    (Fin.last (n + 1)) b last_before w at_end'
  exact ⟨first, last, first_time, last_time,
    fine.blockIndex_lt_of_block_lt (show (0 : Fin (n + 2)) < Fin.last (n + 1) by
      change 0 < n + 1
      omega) first last⟩

end Unfoldings.ConvexRoof.CompletionMesh
