module

public import Unfoldings.Topology.ChainComplement
public import Unfoldings.Topology.ChainConcatSum
public import Unfoldings.Topology.ChainReversal
public import Unfoldings.Complex.LinkCornerWeights

/-! Complementary actual vertex-link intervals partition all original corner weights. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {w : C.Vertex Set.univ} {n m : ℕ}
  (c : (C.linkSystem Set.univ w).Chain n) (d : (C.linkSystem Set.univ w).Chain m)

/-- Complementary actual fan joins partition every original corner contribution.
Neither original interval separation nor whole-star coverage is a supplied certificate. -/
theorem sum_complementary_linkCornerWeight (internal : ¬ C.IsBoundaryVertex Set.univ w)
    (joined : (C.linkSystem Set.univ w).mate ((C.linkSystem Set.univ w).turn c.last) = d.first)
    (closes : (C.linkSystem Set.univ w).mate ((C.linkSystem Set.univ w).turn d.last) = c.first)
    (different : d.first ≠ c.first) (weight : C.Corner → ℝ) :
    (∑ i, weight (c.point i).val.1) + (∑ j, weight (d.point j).val.1) =
      C.regionalCornerSum Set.univ weight w := by
  have free (p : C.LinkGerm Set.univ w) : (C.linkSystem Set.univ w).mate p ≠ p := fun fixed =>
    internal ((C.isBoundaryVertex_iff_linkMate_fixed Set.univ w).mpr ⟨p, fixed⟩)
  obtain ⟨apart, covers⟩ := (C.linkSystem Set.univ w).complementary_chains_partition
    (C.linkSystem_connected Set.univ w) free c d joined closes different
  let whole := c.concat d apart joined
  have coverage (p) : whole.Visited p :=
    (c.concat_visited_iff d apart joined p).mpr (covers p)
  have weights := C.sum_linkCornerWeight w whole coverage weight
  exact (c.sum_concat d apart joined (fun p : C.LinkGerm Set.univ w => weight p.val.1)).symm.trans
    weights

/-- Reversing a link interval preserves every original corner and its weight. -/
theorem sum_reverse_linkCornerWeight (weight : C.Corner → ℝ) :
    (∑ i, weight (d.reverse.point i).val.1) = ∑ j, weight (d.point j).val.1 := by
  change (∑ i : Fin (m + 1), weight (d.point i.rev).val.1) = _
  exact Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (m + 1))) (fun j => weight (d.point j).val.1)

/-- Opposite retained sides have the full original star between them. The endpoint relations
are the actual old seam pairings, and all weights, not only angle sums, are preserved. -/
theorem sum_opposite_linkCornerWeight (internal : ¬ C.IsBoundaryVertex Set.univ w)
    (first : d.first = (C.linkSystem Set.univ w).mate c.first)
    (last : (C.linkSystem Set.univ w).turn d.last =
      (C.linkSystem Set.univ w).mate ((C.linkSystem Set.univ w).turn c.last))
    (different : (C.linkSystem Set.univ w).turn d.last ≠ c.first) (weight : C.Corner → ℝ) :
    (∑ i, weight (c.point i).val.1) + (∑ j, weight (d.point j).val.1) =
      C.regionalCornerSum Set.univ weight w := by
  let P := C.linkSystem Set.univ w
  have joined : P.mate (P.turn c.last) = d.reverse.first := by
    rw [d.reverse_first]
    exact last.symm
  have closes : P.mate (P.turn d.reverse.last) = c.first := by
    rw [d.reverse_last, P.turn_involutive, first, P.mate_involutive]
  have distinct : d.reverse.first ≠ c.first := by
    rw [d.reverse_first]
    exact different
  have weights := C.sum_complementary_linkCornerWeight c d.reverse internal
    joined closes distinct weight
  rw [C.sum_reverse_linkCornerWeight] at weights
  exact weights

end Unfoldings.TriangleComplex
