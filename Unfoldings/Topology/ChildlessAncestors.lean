module

public import Unfoldings.Topology.SelectedSubtree

/-! A childless nonroot has no proper descendants. -/

@[expose] public section

namespace Unfoldings.AscendingParents

variable {V : Type*} (P : AscendingParents V)

theorem parent_ne_childless {leaf : V} (nonroot : leaf ∉ P.roots)
    (childless : ∀ child ∉ P.roots, P.parent child ≠ leaf) (w : V) : P.parent w ≠ leaf := by
  by_cases root : w ∈ P.roots
  · rw [P.fixed_root w root]
    intro same
    exact nonroot (same ▸ root)
  · exact childless w root

theorem ancestor_childless_iff {leaf : V} (nonroot : leaf ∉ P.roots)
    (childless : ∀ child ∉ P.roots, P.parent child ≠ leaf) (w : V) :
    P.Ancestor w leaf ↔ w = leaf := by
  constructor
  · rintro ⟨n, same⟩
    cases n with
    | zero => exact same
    | succ n =>
      rw [Function.iterate_succ_apply'] at same
      exact (P.parent_ne_childless nonroot childless _ same).elim
  · rintro rfl
    exact P.ancestor_refl _

end Unfoldings.AscendingParents
