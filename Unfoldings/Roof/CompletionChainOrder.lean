module

public import Unfoldings.Roof.CompletionChainFanRefinement
public import Unfoldings.Topology.ChainSubsequence

/-! The actual fine path preserves complete coarse bank order, including every fine piece. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  {E : K.CompletionMesh φ region K.originalEdgeEquations}

local instance completionChainOrderIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

variable {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain n}
  (R : E.OriginalChainRefinement retain coarse)

open Classical in
/-- The located old hinge is precisely the first directed fine end of its physical block. -/
theorem coarseIndex_point (i : Fin (n + 1)) :
    R.chain.point (R.coarseIndex i) = (R.block i).chain.first := by
  obtain ⟨j, same⟩ := (R.covered (R.block i).chain.first).mpr ⟨i, 0, rfl⟩
  have image := (R.block i).first_image
  change _ = C.vertexPoint retain (C.boundaryEndVertex retain (R.label i).start) at image
  rw [R.named] at image
  have equal : R.coarseIndex i = j := by
    apply R.index_eq_of_image
    rw [R.coarseIndex_image, same, image]
  exact (congrArg R.chain.point equal).trans same

open Classical in
/-- Distinct old bank indices have distinct actual original bank labels. -/
theorem label_banks_ne {i j : Fin (n + 1)} (different : i ≠ j) :
    (R.label i).bank ≠ (R.label j).bank := by
  intro same
  apply different
  apply C.boundaryChain_banks_injective retain coarse
  dsimp only
  rw [← R.named i, ← R.named j]
  simpa only [TriangleComplex.DirectedCutBank.start, Equiv.apply_symm_apply] using same

open Classical in
/-- Every physical block occurs contiguously in the fine path, without cyclic wrapping. -/
theorem exists_block_embedding (i : Fin (n + 1)) :
    ∃ index : Fin ((R.block i).length + 1) ↪o Fin (R.length + 1),
      (∀ k, R.chain.point (index k) = (R.block i).chain.point k) ∧
      ∀ k, (index k).val = (index 0).val + k.val := by
  apply (R.block i).chain.exists_contiguous_embedding R.chain
  · intro k
    exact (R.covered _).mpr ⟨i, k, rfl⟩
  · intro k same
    have first : R.chain.first = (R.block 0).chain.first := by
      simpa only [R.coarseIndex_zero, PairedInvolutions.System.Chain.first] using
        R.coarseIndex_point 0
    rw [first] at same
    by_cases zero : i = 0
    · subst i
      have equal := (R.block 0).chain.injective same
      exact (Fin.succ_ne_zero k) equal
    · exact ((R.block i).separated (R.block 0) (R.label_banks_ne zero) k.succ 0).1 same

open Classical in
/-- The derived order embedding of every fine piece of one original bank. -/
def blockIndex (i : Fin (n + 1)) :
    Fin ((R.block i).length + 1) ↪o Fin (R.length + 1) :=
  (R.exists_block_embedding i).choose

open Classical in
theorem blockIndex_point (i : Fin (n + 1)) (k : Fin ((R.block i).length + 1)) :
    R.chain.point (R.blockIndex i k) = (R.block i).chain.point k :=
  (R.exists_block_embedding i).choose_spec.1 k

open Classical in
@[simp] theorem blockIndex_zero (i : Fin (n + 1)) : R.blockIndex i 0 = R.coarseIndex i :=
  R.chain.injective ((R.blockIndex_point i 0).trans (R.coarseIndex_point i).symm)

open Classical in
/-- Fine indices have the exact old-block offset, with no reordering or missing pieces. -/
theorem blockIndex_val (i : Fin (n + 1)) (k : Fin ((R.block i).length + 1)) :
    (R.blockIndex i k).val = (R.coarseIndex i).val + k.val := by
  have offset := (R.exists_block_embedding i).choose_spec.2 k
  change (R.blockIndex i k).val = (R.blockIndex i 0).val + k.val at offset
  simpa only [R.blockIndex_zero] using offset

open Classical in
/-- Consecutive old hinges are separated by exactly the preceding block's number of banks. -/
theorem coarseIndex_succ (k : Fin n) :
    (R.coarseIndex k.succ).val =
      (R.coarseIndex k.castSucc).val + (R.block k.castSucc).length + 1 := by
  have different := R.label_banks_ne (show k.castSucc ≠ k.succ by
    intro equal
    have values := congrArg Fin.val equal
    simp only [Fin.val_castSucc, Fin.val_succ] at values
    omega)
  have corner : C.vertexOfCorner retain (R.label k.castSucc).finishCorner =
      C.vertexOfCorner retain (R.label k.succ).startCorner := by
    rw [← (R.label k.castSucc).finish_vertex, ← (R.label k.succ).start_vertex, R.named, R.named]
    have same := (C.boundaryMate_spec retain
      (C.boundaryTurn retain (coarse.point k.castSucc))).2
    have step : C.boundaryMate retain (C.boundaryTurn retain (coarse.point k.castSucc)) =
        coarse.point k.succ := coarse.next k
    rw [step] at same
    exact same.symm
  have next : E.originalComplex.boundaryMate (E.originalRetain retain)
      (E.originalComplex.boundaryTurn (E.originalRetain retain)
        (R.chain.point (R.blockIndex k.castSucc (Fin.last (R.block k.castSucc).length)))) =
      R.chain.point (R.coarseIndex k.succ) := by
    rw [R.blockIndex_point, R.coarseIndex_point]
    exact (R.block k.castSucc).joined (R.block k.succ) different corner
  have nonzero : R.coarseIndex k.succ ≠ 0 := by
    intro equal
    exact (Fin.succ_ne_zero k) (R.coarseIndex_injective (equal.trans R.coarseIndex_zero.symm))
  have step := R.chain.successor_index next nonzero
  rw [R.blockIndex_val, Fin.val_last] at step
  exact step

open Classical in
/-- Old hinges occur in their original order along the physical fine path. -/
theorem coarseIndex_strictMono : StrictMono R.coarseIndex := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro k
  change (R.coarseIndex k.castSucc).val < (R.coarseIndex k.succ).val
  rw [R.coarseIndex_succ]
  omega

end Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement
