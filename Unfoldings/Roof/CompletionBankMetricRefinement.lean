module

public import Unfoldings.Roof.CompletionOrientedBankRolling
public import Unfoldings.Roof.CompletionBankDistinctness

/-! Directed fine bank blocks keep their exact original cut-metric endpoint copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionMetricBankIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- Construct a directed fine block with its actual original cut-vertex endpoint images.
Every whole fine bank occurs exactly once with zero extra real heading, in either
original endpoint order. No endpoint-copy or angle preservation premise is supplied. -/
theorem exists_original_cutBank_metric_refinement (retain : Set C.Seam)
    (s : C.CutSeam retain) (side flag : Bool) :
    ∃ n : ℕ, ∃ chain : (E.originalComplex.boundarySystem (E.originalRetain retain)).Chain n,
      (∀ i, E.originalComplex.boundaryChainRollHeading chain i = 0) ∧
      E.originalMetricEquiv retain (E.originalComplex.vertexPoint (E.originalRetain retain)
        (E.originalComplex.boundaryEndVertex (E.originalRetain retain) chain.first)) =
          C.vertexPoint retain (C.vertexOfCorner retain
            (C.germOfEndpoint (C.seamSide s.val side) flag).1) ∧
      E.originalMetricEquiv retain (E.originalComplex.vertexPoint (E.originalRetain retain)
        (E.originalComplex.boundaryEndVertex (E.originalRetain retain)
          (E.originalComplex.boundaryTurn (E.originalRetain retain) chain.last))) =
          C.vertexPoint retain (C.vertexOfCorner retain
            (C.germOfEndpoint (C.seamSide s.val side) (!flag)).1) ∧
      ∃ index : Fin (n + 1) ≃
          E.faceSidePieces (C.seamSide s.val side).face (C.seamSide s.val side).edge,
        ∀ i, (E.originalComplex.boundaryEndEquiv (E.originalRetain retain) (chain.point i)).1 =
          E.subdividedCutBank retain s side (index i) := by
  let D := E.originalComplex
  let kept := E.originalRetain retain
  let edge := C.seamSide s.val side
  obtain ⟨n, chain, heading, first, last, index, named⟩ :=
    E.exists_oriented_original_cutBank_straight_roll retain s side flag
  have parent (i) : E.originalParent (chain.point i).val.1.1 = edge.face := by
    exact (congrArg (fun bank : D.BoundaryBank kept => E.originalParent bank.val.face)
      (named i)).trans (E.subdividedCutBank_parent retain s side (index i))
  have endpoint (b : Bool) : ((K.projectedTriangle edge.face).endpoint edge.edge b).val =
      (K.projectedTriangle edge.face).vertex (C.germOfEndpoint edge b).1.2 := by
    cases b <;> rfl
  have turn_parent : E.originalParent (D.boundaryTurn kept chain.last).val.1.1 = edge.face := by
    rw [D.boundaryTurn_corner]
    exact parent (Fin.last n)
  have first_image := E.originalMetricEquiv_boundaryEnd_at_corner retain chain.first edge.face
    (C.germOfEndpoint edge flag).1.2 (parent 0) (first.trans (endpoint flag))
  have last_image := E.originalMetricEquiv_boundaryEnd_at_corner retain
    (D.boundaryTurn kept chain.last) edge.face (C.germOfEndpoint edge (!flag)).1.2 turn_parent
      (last.trans (endpoint (!flag)))
  exact ⟨n, chain, heading, first_image, last_image, index, named⟩

end Unfoldings.ConvexRoof.CompletionMesh
