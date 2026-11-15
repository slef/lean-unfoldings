module

public import Unfoldings.Roof.CompletionChainOrder
public import Unfoldings.Complex.BoundaryChainHeadingStep

/-! Every real heading of an actual fine path is the corresponding original bank heading. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  {E : K.CompletionMesh φ region K.originalEdgeEquations}

local instance completionChainPrefixHeadingIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

variable {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain n}
  (R : E.OriginalChainRefinement retain coarse)

open Classical in
/-- No internal fine piece of one original bank adds an intrinsic real turn. -/
theorem block_heading (i : Fin (n + 1)) (k : Fin ((R.block i).length + 1)) :
    E.originalComplex.boundaryChainRollHeading R.chain (R.blockIndex i k) =
      E.originalComplex.boundaryChainRollHeading R.chain (R.coarseIndex i) := by
  induction k using Fin.induction with
  | zero => rw [R.blockIndex_zero]
  | succ k previous =>
    have next : (R.blockIndex i k.succ).val = (R.blockIndex i k.castSucc).val + 1 := by
      rw [R.blockIndex_val, R.blockIndex_val]
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    have step := E.originalComplex.boundaryChainRollHeading_step_of_indices R.chain next
    have straight := E.originalComplex.boundaryChain_internal_angle_of_zero_heading
      (R.block i).chain (R.block i).zero_heading k
    rw [R.blockIndex_point, straight, sub_self, add_zero] at step
    exact step.trans previous

open Classical in
/-- Every old hinge prefix retains its exact unreduced heading in the physical fine path. -/
theorem coarseIndex_heading (i : Fin (n + 1)) :
    E.originalComplex.boundaryChainRollHeading R.chain (R.coarseIndex i) =
      C.boundaryChainRollHeading coarse i := by
  induction i using Fin.induction with
  | zero => rw [R.coarseIndex_zero]; rfl
  | succ k previous =>
    have next : (R.coarseIndex k.succ).val =
        (R.blockIndex k.castSucc (Fin.last (R.block k.castSucc).length)).val + 1 := by
      rw [R.coarseIndex_succ, R.blockIndex_val, Fin.val_last]
    have step := E.originalComplex.boundaryChainRollHeading_step_of_indices R.chain next
    rw [R.block_heading, R.coarseIndex_totalAngle, previous] at step
    exact step.trans (Fin.partialSum_succ (fun k : Fin n =>
      Real.pi - C.totalAngle retain (C.boundaryEndVertex retain (coarse.point k.succ))) k).symm

open Classical in
/-- Every fine bank piece has precisely its original bank's real heading. -/
theorem block_heading_eq_coarse (i : Fin (n + 1)) (k : Fin ((R.block i).length + 1)) :
    E.originalComplex.boundaryChainRollHeading R.chain (R.blockIndex i k) =
      C.boundaryChainRollHeading coarse i :=
  (R.block_heading i k).trans (R.coarseIndex_heading i)

open Classical in
/-- The contiguous blocks exhaust the entire actual fine path. -/
theorem blockIndex_coverage (j : Fin (R.length + 1)) :
    ∃ i k, R.blockIndex i k = j := by
  obtain ⟨i, k, same⟩ := (R.covered (R.chain.point j)).mp ⟨j, rfl⟩
  exact ⟨i, k, R.chain.injective ((R.blockIndex_point i k).trans same)⟩

open Classical in
/-- Subdivision preserves the entire set of real bank headings, including full rotations. -/
theorem heading_range_eq :
    Set.range (E.originalComplex.boundaryChainRollHeading R.chain) =
      Set.range (C.boundaryChainRollHeading coarse) := by
  ext angle
  constructor
  · rintro ⟨j, equal⟩
    obtain ⟨i, k, at_j⟩ := R.blockIndex_coverage j
    exact ⟨i, (R.block_heading_eq_coarse i k).symm.trans (by rw [at_j]; exact equal)⟩
  · rintro ⟨i, equal⟩
    exact ⟨R.coarseIndex i, (R.coarseIndex_heading i).trans equal⟩

end Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement
