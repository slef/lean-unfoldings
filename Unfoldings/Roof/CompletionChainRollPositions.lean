module

public import Unfoldings.Roof.CompletionChainLength
public import Unfoldings.Topology.FinitePrefixSum

/-! Exact positions of all original and inserted vertices in the whole intrinsic fine roll. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  {E : K.CompletionMesh φ region K.originalEdgeEquations}

local instance completionChainRollPositionsIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

variable {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain n}
  (R : E.OriginalChainRefinement retain coarse)

open Classical in
/-- Include the true far endpoint in the numerical placement of one fine bank block. -/
def blockVertexIndex (i : Fin (n + 1)) (k : Fin ((R.block i).length + 2)) :
    Fin (R.length + 2) :=
  ⟨(R.coarseIndex i).val + k.val, by
    have bound := (R.blockIndex i (Fin.last (R.block i).length)).isLt
    rw [R.blockIndex_val, Fin.val_last] at bound
    have at_k := k.isLt
    omega⟩

open Classical in
theorem blockVertexIndex_castSucc (i : Fin (n + 1)) (k : Fin ((R.block i).length + 1)) :
    R.blockVertexIndex i k.castSucc = (R.blockIndex i k).castSucc := by
  apply Fin.ext
  exact (R.blockIndex_val i k).symm

open Classical in
theorem blockVertexIndex_succ (i : Fin (n + 1)) (k : Fin ((R.block i).length + 1)) :
    R.blockVertexIndex i k.succ = (R.blockIndex i k).succ := by
  apply Fin.ext
  change (R.coarseIndex i).val + (k.val + 1) = (R.blockIndex i k).val + 1
  rw [R.blockIndex_val]
  omega

open Classical in
@[simp] theorem blockVertexIndex_zero (i : Fin (n + 1)) :
    R.blockVertexIndex i 0 = (R.coarseIndex i).castSucc := Fin.ext (Nat.add_zero _)

open Classical in
/-- Intrinsic lengths in the actual original bank order. -/
def blockLengths (i : Fin (n + 1)) (k : Fin ((R.block i).length + 1)) : ℝ :=
  E.originalComplex.boundaryBankLength ((R.block i).chain.point k)

open Classical in
/-- All fine block vertices are placed by their actual cumulative intrinsic arclength. -/
theorem block_roll_vertex (i : Fin (n + 1)) (k : Fin ((R.block i).length + 2)) :
    (E.originalComplex.boundaryChainRoll R.chain).vertex (R.blockVertexIndex i k) =
      (E.originalComplex.boundaryChainRoll R.chain).vertex (R.coarseIndex i).castSucc +
        ((Fin.partialSum (R.blockLengths i) k : ℝ) : ℂ) *
          polarRay (C.boundaryChainRollHeading coarse i) := by
  induction k using Fin.induction with
  | zero => rw [R.blockVertexIndex_zero, Fin.partialSum_zero, Complex.ofReal_zero,
      zero_mul, add_zero]
  | succ k previous =>
    have step :
        (E.originalComplex.boundaryChainRoll R.chain).vertex (R.blockVertexIndex i k.succ) -
          (E.originalComplex.boundaryChainRoll R.chain).vertex
            (R.blockVertexIndex i k.castSucc) =
              (R.blockLengths i k : ℂ) * polarRay (C.boundaryChainRollHeading coarse i) := by
      rw [R.blockVertexIndex_succ, R.blockVertexIndex_castSucc]
      change (E.originalComplex.boundaryChainRoll R.chain).edge (R.blockIndex i k) = _
      simp only [TriangleComplex.boundaryChainRoll, PolygonalChain.ofHeadings_edge,
        R.block_heading_eq_coarse, R.blockIndex_point, blockLengths]
    rw [Fin.partialSum_succ, Complex.ofReal_add, add_mul]
    linear_combination previous + step

open Classical in
/-- The true endpoint of a fine block is the initial rolled position plus the entire old edge. -/
theorem block_roll_endpoint (i : Fin (n + 1)) :
    (E.originalComplex.boundaryChainRoll R.chain).vertex
        (R.blockVertexIndex i (Fin.last ((R.block i).length + 1))) =
      (E.originalComplex.boundaryChainRoll R.chain).vertex (R.coarseIndex i).castSucc +
        (C.boundaryChainRoll coarse).edge i := by
  have total : Fin.partialSum (R.blockLengths i) (Fin.last ((R.block i).length + 1)) =
      C.boundaryBankLength (coarse.point i) :=
    (fin_partialSum_prefix le_rfl _ _ (fun _ => rfl)).trans (R.block_sum_lengths i)
  rw [R.block_roll_vertex, total]
  simp only [TriangleComplex.boundaryChainRoll, PolygonalChain.ofHeadings_edge]

open Classical in
/-- Every original starting vertex has its exact original position in the whole refined roll. -/
theorem coarseIndex_roll_vertex (i : Fin (n + 1)) :
    (E.originalComplex.boundaryChainRoll R.chain).vertex (R.coarseIndex i).castSucc =
      (C.boundaryChainRoll coarse).vertex i.castSucc := by
  induction i using Fin.induction with
  | zero =>
    rw [R.coarseIndex_zero]
    rfl
  | succ k previous =>
    have at_next : R.blockVertexIndex k.castSucc (Fin.last ((R.block k.castSucc).length + 1)) =
        (R.coarseIndex k.succ).castSucc := by
      apply Fin.ext
      change (R.coarseIndex k.castSucc).val + ((R.block k.castSucc).length + 1) =
        (R.coarseIndex k.succ).val
      rw [R.coarseIndex_succ]
      omega
    have step := R.block_roll_endpoint k.castSucc
    rw [at_next, previous, PolygonalChain.edge, Fin.succ_castSucc] at step
    linear_combination step

open Classical in
/-- Each inserted rolled vertex lies at the original bank's exact cumulative arclength. -/
theorem block_roll_vertex_eq_coarse (i : Fin (n + 1)) (k : Fin ((R.block i).length + 2)) :
    (E.originalComplex.boundaryChainRoll R.chain).vertex (R.blockVertexIndex i k) =
      (C.boundaryChainRoll coarse).vertex i.castSucc +
        ((Fin.partialSum (R.blockLengths i) k : ℝ) : ℂ) *
          polarRay (C.boundaryChainRollHeading coarse i) := by
  rw [R.block_roll_vertex, R.coarseIndex_roll_vertex]

end Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement
