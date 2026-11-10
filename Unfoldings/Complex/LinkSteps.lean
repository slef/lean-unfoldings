module

public import Unfoldings.Complex.LinkOrdering

/-! Consecutive ordered link corners cross actual retained original seams. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain) {n : ℕ}
  (c : (C.linkSystem retain v).Chain n)

theorem chain_next_crosses (k : Fin n) :
    C.GermCrosses retain (C.turnGerm (c.point k.castSucc).val) (c.point k.succ).val := by
  classical
  have different : C.linkMate retain v (C.linkTurn retain v (c.point k.castSucc)) ≠
      C.linkTurn retain v (c.point k.castSucc) := by
    change (C.linkSystem retain v).mate ((C.linkSystem retain v).turn (c.point k.castSucc)) ≠
      (C.linkSystem retain v).turn (c.point k.castSucc)
    rw [c.next k]
    exact c.disjoint k.succ k.castSucc
  by_cases paired : ∃ q, C.GermCrosses retain (C.turnGerm (c.point k.castSucc).val) q
  · obtain ⟨q, crossing⟩ := paired
    have equal := congrArg Subtype.val (c.next k)
    change C.mateGerm retain (C.turnGerm (c.point k.castSucc).val) = _ at equal
    rw [C.mateGerm_of_crossing crossing] at equal
    exact equal ▸ crossing
  · have fixed : C.mateGerm retain (C.turnGerm (c.point k.castSucc).val) =
        C.turnGerm (c.point k.castSucc).val := by
      simp only [mateGerm, dite_eq_right paired]
    exact (different (Subtype.ext fixed)).elim

end Unfoldings.TriangleComplex
