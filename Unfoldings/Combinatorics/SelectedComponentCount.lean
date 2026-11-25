module

public import Unfoldings.Combinatorics.ActiveGraphComponents
public import Mathlib.SetTheory.Cardinal.Finite

/-! Isolated unselected vertices contribute one component each. -/

@[expose] public section

namespace Unfoldings

/-- Count the components meeting an active vertex set plus the isolated vertices
outside it. This covers an empty active set or multiple active components. -/
theorem card_components_eq_selected_add_card_isolated {V : Type*} [Finite V]
    (G : SimpleGraph V) (active : V → Prop)
    (internal : ∀ {v w}, G.Adj v w → active v) :
    Nat.card G.ConnectedComponent =
      Nat.card {c : G.ConnectedComponent // ∃ v, active v ∧ G.connectedComponentMk v = c} +
        Nat.card {v // ¬ active v} := by
  classical
  let occupied (c : G.ConnectedComponent) := ∃ v, active v ∧ G.connectedComponentMk v = c
  have isolated (v w : V) (outside : ¬ active v) (reach : G.Reachable v w) : v = w := by
    obtain ⟨walk⟩ := reach
    cases walk with
    | nil => rfl
    | cons edge _ => exact (outside (internal edge)).elim
  let outside : {v // ¬ active v} → {c // ¬ occupied c} := fun v =>
    ⟨G.connectedComponentMk v.val, by
      rintro ⟨w, member, together⟩
      have eq := isolated v.val w v.property (SimpleGraph.ConnectedComponent.exact together.symm)
      exact v.property (eq.symm ▸ member)⟩
  have bijective : Function.Bijective outside := by
    constructor
    · intro v w same
      exact Subtype.ext (isolated v.val w.val v.property
        (SimpleGraph.ConnectedComponent.exact (congrArg Subtype.val same)))
    · rintro ⟨c, empty⟩
      obtain ⟨v, rfl⟩ := c.exists_rep
      exact ⟨⟨v, fun h => empty ⟨v, h, rfl⟩⟩, rfl⟩
  let equivalence := Equiv.ofBijective outside bijective
  change Nat.card G.ConnectedComponent = Nat.card {c // occupied c} + Nat.card {v // ¬ active v}
  rw [← Nat.card_congr (Equiv.sumCompl occupied), Nat.card_sum, ← Nat.card_congr equivalence]

end Unfoldings
