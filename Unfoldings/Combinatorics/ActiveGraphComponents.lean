module

public import Unfoldings.Combinatorics.GraphCycleRank
public import Mathlib.Data.Fintype.Option

/-! Removing the isolated vertices from a finite graph. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- If all edges lie among the active vertices and those vertices form one
nonempty connected component, all other components are singletons. -/
theorem card_components_eq_one_add_card_inactive {V : Type*} [Finite V]
    (G : SimpleGraph V) (active : V → Prop)
    (internal : ∀ {v w}, G.Adj v w → active v)
    (nonempty : ∃ v, active v)
    (connected : ∀ v w, active v → active w → G.Reachable v w) :
    Nat.card G.ConnectedComponent = 1 + Nat.card {v // ¬ active v} := by
  classical
  obtain ⟨base, base_active⟩ := nonempty
  let index : Option {v // ¬ active v} → G.ConnectedComponent
    | none => G.connectedComponentMk base
    | some v => G.connectedComponentMk v.val
  have isolated (a b : V) (outside : ¬ active a) (reach : G.Reachable a b) : a = b := by
    obtain ⟨walk⟩ := reach
    cases walk with
    | nil => rfl
    | cons edge _ => exact (outside (internal edge)).elim
  have bijective : Function.Bijective index := by
    constructor
    · intro a b equal
      cases a with
      | none =>
        cases b with
        | none => rfl
        | some b =>
          have reach := SimpleGraph.ConnectedComponent.exact equal.symm
          exact (b.property ((isolated _ _ b.property reach).symm ▸ base_active)).elim
      | some a =>
        cases b with
        | none =>
          have reach := SimpleGraph.ConnectedComponent.exact equal
          exact (a.property ((isolated _ _ a.property reach).symm ▸ base_active)).elim
        | some b =>
          have reach := SimpleGraph.ConnectedComponent.exact equal
          exact congrArg some (Subtype.ext (isolated _ _ a.property reach))
    · intro c
      obtain ⟨v, rfl⟩ := c.exists_rep
      by_cases h : active v
      · exact ⟨none, SimpleGraph.ConnectedComponent.sound (connected _ _ base_active h)⟩
      · exact ⟨some ⟨v, h⟩, rfl⟩
  let : Fintype {v // ¬ active v} := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.ofBijective index bijective), Nat.card_eq_fintype_card,
    Fintype.card_option, ← Nat.card_eq_fintype_card, Nat.add_comm]

end Unfoldings
