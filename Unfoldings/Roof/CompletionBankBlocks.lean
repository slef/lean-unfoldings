module

public import Unfoldings.Roof.CompletionBankMetricRefinement
public import Unfoldings.Roof.CompletionBankBlockJoins
public import Unfoldings.Topology.ChainConcatenation

/-! Construct and concatenate actual directed fine bank blocks in the original cut metric. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionBankBlocksIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- A complete directed physical refinement, with all data constructed by `originalBankBlock`. -/
structure OriginalBankBlock (retain : Set C.Seam) (s : C.CutSeam retain) (side flag : Bool) where
  length : ℕ
  chain : (E.originalComplex.boundarySystem (E.originalRetain retain)).Chain length
  index : Fin (length + 1) ≃
    E.faceSidePieces (C.seamSide s.val side).face (C.seamSide s.val side).edge
  named : ∀ i, (E.originalComplex.boundaryEndEquiv (E.originalRetain retain) (chain.point i)).1 =
    E.subdividedCutBank retain s side (index i)
  zero_heading : ∀ i, E.originalComplex.boundaryChainRollHeading chain i = 0
  first_image : E.originalMetricEquiv retain
    (E.originalComplex.vertexPoint (E.originalRetain retain)
      (E.originalComplex.boundaryEndVertex (E.originalRetain retain) chain.first)) =
        C.vertexPoint retain (C.vertexOfCorner retain
          (C.germOfEndpoint (C.seamSide s.val side) flag).1)
  last_image : E.originalMetricEquiv retain
    (E.originalComplex.vertexPoint (E.originalRetain retain)
      (E.originalComplex.boundaryEndVertex (E.originalRetain retain)
        (E.originalComplex.boundaryTurn (E.originalRetain retain) chain.last))) =
          C.vertexPoint retain (C.vertexOfCorner retain
            (C.germOfEndpoint (C.seamSide s.val side) (!flag)).1)

open Classical in
/-- Construct every actual piece, directed order, endpoint copy and real rolling value. -/
def originalBankBlock (retain : Set C.Seam) (s : C.CutSeam retain) (side flag : Bool) :
    E.OriginalBankBlock retain s side flag :=
  Classical.choice (by
    obtain ⟨n, chain, heading, first, last, index, named⟩ :=
      E.exists_original_cutBank_metric_refinement retain s side flag
    exact ⟨⟨n, chain, index, named, heading, first, last⟩⟩)

namespace OriginalBankBlock

variable {E} {retain : Set C.Seam} {s t : C.CutSeam retain} {side flag other nextFlag : Bool}
  (A : E.OriginalBankBlock retain s side flag) (B : E.OriginalBankBlock retain t other nextFlag)

open Classical in
/-- Original bank distinctness derives the separation needed for actual chain concatenation. -/
theorem separated (different : C.cutBank retain s side ≠ C.cutBank retain t other) :
    ∀ i j, A.chain.point i ≠ B.chain.point j ∧
      A.chain.point i ≠ E.originalComplex.boundaryTurn
        (E.originalRetain retain) (B.chain.point j) :=
  fun i j => E.original_bank_blocks_separated retain s t side other different
    (A.index i) (B.index j) _ _ (A.named i) (B.named j)

open Classical in
/-- A shared original cut-corner class constructs the actual fine successor between blocks. -/
theorem joined (different : C.cutBank retain s side ≠ C.cutBank retain t other)
    (corner : C.vertexOfCorner retain (C.germOfEndpoint (C.seamSide s.val side) (!flag)).1 =
      C.vertexOfCorner retain (C.germOfEndpoint (C.seamSide t.val other) nextFlag).1) :
    E.originalComplex.boundaryMate (E.originalRetain retain)
      (E.originalComplex.boundaryTurn (E.originalRetain retain) A.chain.last) = B.chain.first := by
  let D := E.originalComplex
  let kept := E.originalRetain retain
  have vertices : D.boundaryEndVertex kept B.chain.first =
      D.boundaryEndVertex kept (D.boundaryTurn kept A.chain.last) := by
    apply D.vertexPoint_injective kept
    apply (E.originalMetricEquiv retain).injective
    rw [B.first_image, A.last_image, corner]
  have distinct : B.chain.first ≠ D.boundaryTurn kept A.chain.last := by
    intro same
    have reverse := congrArg (D.boundaryTurn kept) same
    rw [D.boundaryTurn_involutive] at reverse
    exact (A.separated B different (Fin.last A.length) 0).2 reverse.symm
  exact ((D.exists_unique_other_boundaryEnd kept
    (D.boundaryTurn kept A.chain.last)).unique ⟨distinct, vertices⟩
      (D.boundaryMate_spec kept _)).symm

open Classical in
/-- Concatenate concrete physical refinements using only original bank labels and corner copies. -/
def concat (different : C.cutBank retain s side ≠ C.cutBank retain t other)
    (corner : C.vertexOfCorner retain (C.germOfEndpoint (C.seamSide s.val side) (!flag)).1 =
      C.vertexOfCorner retain (C.germOfEndpoint (C.seamSide t.val other) nextFlag).1) :
    (E.originalComplex.boundarySystem (E.originalRetain retain)).Chain (A.length + B.length + 1) :=
  A.chain.concat B.chain (A.separated B different) (A.joined B different corner)

open Classical in
@[simp] theorem concat_first (different : C.cutBank retain s side ≠ C.cutBank retain t other)
    (corner : C.vertexOfCorner retain (C.germOfEndpoint (C.seamSide s.val side) (!flag)).1 =
      C.vertexOfCorner retain (C.germOfEndpoint (C.seamSide t.val other) nextFlag).1) :
    (A.concat B different corner).first = A.chain.first :=
  A.chain.concat_first B.chain _ _

open Classical in
@[simp] theorem concat_last (different : C.cutBank retain s side ≠ C.cutBank retain t other)
    (corner : C.vertexOfCorner retain (C.germOfEndpoint (C.seamSide s.val side) (!flag)).1 =
      C.vertexOfCorner retain (C.germOfEndpoint (C.seamSide t.val other) nextFlag).1) :
    (A.concat B different corner).last = B.chain.last :=
  A.chain.concat_last B.chain _ _

end OriginalBankBlock
end Unfoldings.ConvexRoof.CompletionMesh
