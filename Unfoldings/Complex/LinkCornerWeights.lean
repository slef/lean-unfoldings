module

public import Unfoldings.Complex.LinkOrdering
public import Unfoldings.Complex.RegionalCorners

/-! An actual covering link order sums arbitrary original corner weights exactly once. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

open Classical in
/-- Retain every original contribution on the actual full vertex fan. -/
theorem sum_linkCornerWeight (w : C.Vertex Set.univ) {n : ℕ}
    (c : (C.linkSystem Set.univ w).Chain n) (covers : ∀ p, c.Visited p)
    (weight : C.Corner → ℝ) :
    (∑ i : Fin (n + 1), weight (c.point i).val.1) = C.regionalCornerSum Set.univ weight w := by
  classical
  have reindex := (C.linkCornerEquiv Set.univ w c covers).sum_comp
    (fun a : C.CornerAt Set.univ w => weight a.val)
  change (∑ i, weight (c.point i).val.1) = _ at reindex
  have formula : C.regionalCornerSum Set.univ weight w =
      ∑ a : C.CornerAt Set.univ w, weight a.val := by
    simp only [regionalCornerSum, Set.mem_univ, true_and]
    exact (Finset.sum_filter _ _).symm.trans
      (Finset.sum_subtype (Finset.univ.filter (fun a => C.vertexOfCorner Set.univ a = w))
        (by simp) weight)
  exact reindex.trans formula.symm

end Unfoldings.TriangleComplex
