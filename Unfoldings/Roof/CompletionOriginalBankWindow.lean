module

public import Unfoldings.Roof.MarkedOriginalBankWindows
public import Unfoldings.Complex.BoundaryChainIntervalHeading

/-! Actual trimmed bank windows preserve every original internal real turn. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  {E : K.CompletionMesh φ region K.originalEdgeEquations}

local instance originalBankWindowIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

variable {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain (n + 1)}
  (R : E.OriginalChainRefinement retain coarse)

open Classical in
/-- Actual marked endpoint indices and their exact original bank parameters.
`markedOriginalBankWindow` constructs these fields from physical line constraints. -/
structure TrimmedBankWindow (a b : unitInterval) where
  firstPiece : Fin ((R.block 0).length + 1)
  lastPiece : Fin ((R.block (Fin.last (n + 1))).length + 1)
  first_time : R.blockParameter 0 firstPiece.castSucc = a
  last_time : R.blockParameter (Fin.last (n + 1)) lastPiece.castSucc = b

namespace TrimmedBankWindow

variable {R} {a b : unitInterval} (W : R.TrimmedBankWindow a b)

open Classical in
def firstIndex : Fin (R.length + 1) := R.blockIndex 0 W.firstPiece

open Classical in
/-- This is the exclusive final index: the bank beginning at the last trim is omitted. -/
def lastIndex : Fin (R.length + 1) := R.blockIndex (Fin.last (n + 1)) W.lastPiece

open Classical in
theorem ordered : W.firstIndex < W.lastIndex :=
  R.blockIndex_lt_of_block_lt (show (0 : Fin (n + 2)) < Fin.last (n + 1) by
    change 0 < n + 1
    omega) W.firstPiece W.lastPiece

open Classical in
def length : ℕ := W.lastIndex.val - W.firstIndex.val - 1

open Classical in
theorem fits : W.firstIndex.val + W.length ≤ R.length := by
  have order := W.ordered
  have bound := W.lastIndex.isLt
  dsimp only [length]
  change W.firstIndex.val < W.lastIndex.val at order
  omega

open Classical in
/-- The actual interval between the two marked original bank copies. -/
def chain : (E.originalComplex.boundarySystem (E.originalRetain retain)).Chain W.length :=
  R.chain.interval W.firstIndex.val W.length W.fits

open Classical in
@[simp] theorem first : W.chain.first = R.chain.point W.firstIndex := by
  exact (R.chain.interval_first W.firstIndex.val W.length W.fits).trans
    (congrArg R.chain.point (Fin.ext rfl))

open Classical in
/-- A positive final trim lies after the start of its original final bank. -/
theorem lastPiece_pos (positive : 0 < b.val) : 0 < W.lastPiece.val := by
  by_contra absent
  have zero : W.lastPiece.castSucc = 0 := Fin.ext (by change W.lastPiece.val = 0; omega)
  have at_b := W.last_time
  rw [zero, R.blockParameter_zero] at at_b
  have value := congrArg Subtype.val at_b
  change 0 = b.val at value
  linarith

open Classical in
def previousPiece (positive : 0 < b.val) : Fin ((R.block (Fin.last (n + 1))).length + 1) :=
  ⟨W.lastPiece.val - 1, by
    have bound := W.lastPiece.isLt
    have previous := W.lastPiece_pos positive
    omega⟩

open Classical in
theorem interval_first_index :
    R.chain.intervalIndex W.firstIndex.val W.length W.fits 0 = W.firstIndex :=
  Fin.ext (Nat.add_zero _)

open Classical in
theorem interval_last_index (positive : 0 < b.val) :
    R.chain.intervalIndex W.firstIndex.val W.length W.fits (Fin.last W.length) =
      R.blockIndex (Fin.last (n + 1)) (W.previousPiece positive) := by
  apply Fin.ext
  change W.firstIndex.val + W.length =
    (R.blockIndex (Fin.last (n + 1)) (W.previousPiece positive)).val
  have order := W.ordered
  change W.firstIndex.val < W.lastIndex.val at order
  have last_value : W.lastIndex.val =
      (R.coarseIndex (Fin.last (n + 1))).val + W.lastPiece.val :=
    R.blockIndex_val _ _
  have final_value := R.blockIndex_val (Fin.last (n + 1)) (W.previousPiece positive)
  have positive_piece := W.lastPiece_pos positive
  dsimp only [length, previousPiece, Fin.val_mk] at *
  omega

open Classical in
/-- Trimming inserts no new real turn: the whole original terminal heading is retained. -/
theorem terminal_heading_eq (positive : 0 < b.val) :
    E.originalComplex.boundaryChainRollHeading W.chain (Fin.last W.length) =
      C.boundaryChainRollHeading coarse (Fin.last (n + 1)) := by
  have formula := E.originalComplex.boundaryChainRollHeading_interval R.chain
    W.firstIndex.val W.length W.fits (Fin.last W.length)
  rw [W.interval_first_index, W.interval_last_index positive] at formula
  have start : E.originalComplex.boundaryChainRollHeading R.chain W.firstIndex = 0 :=
    R.block_heading_eq_coarse 0 W.firstPiece
  have finish := R.block_heading_eq_coarse (Fin.last (n + 1)) (W.previousPiece positive)
  exact formula.trans (by rw [finish, start, sub_zero])

end TrimmedBankWindow
end Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {retain : Set C.Seam} {n : ℕ}
  (coarse : (C.boundarySystem retain).Chain (n + 1))
  (cut : ∀ i, ¬ C.IsBoundaryEdge Set.univ (C.germEdge (coarse.point i).val))
  (a b : unitInterval) (q c : Plane)

local notation "Q" => PolygonalChain.trimEnds
  (SpatialFolding.projectedBoundaryChain K.folding coarse) a b

open Classical in
/-- Original marked closure lines construct the actual trimmed intrinsic bank window.
No fine-bank indices, side assignments or real-turn preservation are supplied. -/
def markedOriginalBankWindow (first_before : a.val < 1) (last_before : b.val < 1)
    (jordan : Schoenflies.IsJordanCurve ((Q).threeSegmentClosure q c))
    (E : K.CompletionMesh φ (PlanarTopology.closedJordanDomain ((Q).threeSegmentClosure q c))
      (K.combinedCompletionEquations ((Q).markedClosureEquations q c))) :
    (E.originalConstraintView.originalChainRefinement retain coarse cut).TrimmedBankWindow a b := by
  apply Classical.choice
  obtain ⟨first, last, first_time, last_time, _ordered⟩ :=
    exists_trimmed_original_bank_indices coarse cut a b q c first_before last_before jordan E
  exact ⟨⟨first, last, first_time, last_time⟩⟩

end Unfoldings.ConvexRoof.CompletionMesh
