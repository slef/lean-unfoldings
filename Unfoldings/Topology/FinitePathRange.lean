module

public import Mathlib.Topology.Path
public import Mathlib.Order.Fin.Basic

/-! Concatenating a finite sequence of actual paths retains precisely their original carriers. -/

@[expose] public section

namespace Unfoldings

variable {X : Type*} [TopologicalSpace X]

/-- Concatenate named original links in their exact finite order. -/
noncomputable def finitePathConcat : {n : ℕ} → (point : Fin (n + 1) → X) →
    ((i : Fin n) → Path (point i.castSucc) (point i.succ)) →
    Path (point 0) (point (Fin.last n))
  | 0, point, _ => Path.refl (point 0)
  | n + 1, point, link =>
    (finitePathConcat (point ∘ Fin.castSucc) (fun i => link i.castSucc)).trans (link (Fin.last n))

/-- The initial point is retained even for the empty sequence of paths. -/
theorem path_concat_range {n : ℕ} (point : Fin (n + 1) → X)
    (link : (i : Fin n) → Path (point i.castSucc) (point i.succ)) :
    Set.range (finitePathConcat point link) = {point 0} ∪ ⋃ i, Set.range (link i) := by
  induction n with
  | zero => simp only [finitePathConcat, Path.refl_range, Set.iUnion_of_empty, Set.union_empty]
  | succ n ih =>
    rw [finitePathConcat]
    change Set.range ((finitePathConcat (point ∘ Fin.castSucc) (fun i => link i.castSucc)).trans
      (link (Fin.last n))) = _
    rw [Path.trans_range, ih]
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ((first | ⟨i, t, at_x⟩) | ⟨t, at_x⟩)
      · exact Or.inl first
      · exact Or.inr ⟨i.castSucc, t, at_x⟩
      · exact Or.inr ⟨Fin.last n, t, at_x⟩
    · rintro (first | ⟨i, t, at_x⟩)
      · exact Or.inl (Or.inl first)
      · revert at_x
        refine Fin.lastCases ?_ (fun j => ?_) i
        · intro at_x
          exact Or.inr ⟨t, at_x⟩
        · intro at_x
          exact Or.inl (Or.inr ⟨j, t, at_x⟩)

end Unfoldings
