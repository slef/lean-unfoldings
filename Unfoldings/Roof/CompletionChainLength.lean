module

public import Unfoldings.Roof.CompletionChainPrefixHeading
public import Unfoldings.Roof.CompletionChainTrace
public import Unfoldings.Roof.CompletionBankLength
public import Unfoldings.Complex.BoundaryChainAperture
public import Unfoldings.Geometry.PolygonalLength

/-! The whole physical fine bank path preserves intrinsic arclength and rolled displacement. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  {E : K.CompletionMesh φ region K.originalEdgeEquations}

local instance completionChainLengthIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

variable {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain n}
  (R : E.OriginalChainRefinement retain coarse)

open Classical in
/-- Every bank has exactly one original-bank and fine-piece index. -/
def bankIndexEquiv : (Σ i : Fin (n + 1), Fin ((R.block i).length + 1)) ≃
    Fin (R.length + 1) :=
  Equiv.ofBijective (fun a => R.blockIndex a.1 a.2) (by
    constructor
    · rintro ⟨i, k⟩ ⟨j, l⟩ same
      change R.blockIndex i k = R.blockIndex j l at same
      have old : i = j := by
        by_contra different
        apply ((R.block i).separated (R.block j) (R.label_banks_ne different) k l).1
        rw [← R.blockIndex_point, ← R.blockIndex_point, same]
      subst j
      have fine := (R.blockIndex i).injective same
      subst l
      rfl
    · intro j
      obtain ⟨i, k, same⟩ := R.blockIndex_coverage j
      exact ⟨⟨i, k⟩, same⟩)

open Classical in
/-- The lengths in a whole physical block sum to its actual original bank length. -/
theorem block_sum_lengths (i : Fin (n + 1)) :
    (∑ k, E.originalComplex.boundaryBankLength ((R.block i).chain.point k)) =
      C.boundaryBankLength (coarse.point i) := by
  rw [C.boundaryBankLength_eq_edge]
  have edge := congrArg (fun bank : C.BoundaryBank retain => bank.val) (R.label_bank i)
  change C.germEdge (coarse.point i).val = C.seamSide (R.label i).seam.val (R.label i).side at edge
  rw [edge]
  exact (R.block i).sum_bank_lengths

open Classical in
/-- No original bank length is lost or duplicated by physical whole-path refinement. -/
theorem sum_bank_lengths :
    (∑ j, E.originalComplex.boundaryBankLength (R.chain.point j)) =
      ∑ i, C.boundaryBankLength (coarse.point i) := by
  calc
    _ = ∑ a : Σ i : Fin (n + 1), Fin ((R.block i).length + 1),
        E.originalComplex.boundaryBankLength (R.chain.point (R.bankIndexEquiv a)) :=
      (Equiv.sum_comp R.bankIndexEquiv _).symm
    _ = ∑ i, ∑ k : Fin ((R.block i).length + 1),
        E.originalComplex.boundaryBankLength ((R.block i).chain.point k) := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      change E.originalComplex.boundaryBankLength (R.chain.point (R.blockIndex i k)) = _
      rw [R.blockIndex_point]
    _ = _ := Finset.sum_congr rfl (fun i _ => R.block_sum_lengths i)

open Classical in
/-- The developed fine path has the exact total arclength of the original rolled path. -/
theorem roll_length_eq :
    (E.originalComplex.boundaryChainRoll R.chain).projectedLength =
      (C.boundaryChainRoll coarse).projectedLength := by
  simp only [PolygonalChain.projectedLength, TriangleComplex.boundaryChainRoll_edge_length]
  exact R.sum_bank_lengths

open Classical in
/-- Each original bank's fine edge vectors sum to its whole original rolled edge. -/
theorem sum_block_roll_edges (i : Fin (n + 1)) :
    (∑ k : Fin ((R.block i).length + 1),
      (E.originalComplex.boundaryChainRoll R.chain).edge (R.blockIndex i k)) =
        (C.boundaryChainRoll coarse).edge i := by
  simp only [TriangleComplex.boundaryChainRoll, PolygonalChain.ofHeadings_edge,
    R.block_heading_eq_coarse, R.blockIndex_point]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, R.block_sum_lengths]

open Classical in
/-- The whole refined roll has exactly the same endpoint as the original roll. -/
theorem roll_endpoint_eq :
    (E.originalComplex.boundaryChainRoll R.chain).vertex (Fin.last (R.length + 1)) =
      (C.boundaryChainRoll coarse).vertex (Fin.last (n + 1)) := by
  have sums : (∑ j, (E.originalComplex.boundaryChainRoll R.chain).edge j) =
      ∑ i, (C.boundaryChainRoll coarse).edge i := by
    calc
      _ = ∑ a : Σ i : Fin (n + 1), Fin ((R.block i).length + 1),
          (E.originalComplex.boundaryChainRoll R.chain).edge (R.bankIndexEquiv a) :=
        (Equiv.sum_comp R.bankIndexEquiv _).symm
      _ = _ := by
        rw [Fintype.sum_sigma]
        exact Finset.sum_congr rfl (fun i _ => R.sum_block_roll_edges i)
  rw [PolygonalChain.sum_edge, PolygonalChain.sum_edge] at sums
  simpa only [TriangleComplex.boundaryChainRoll, PolygonalChain.ofHeadings_start, sub_zero]
    using sums

end Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement
