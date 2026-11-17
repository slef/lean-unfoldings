module

public import Mathlib.Topology.Connected.Basic

/-! A continuous connected lift cannot switch between two disjoint closed branches. -/

@[expose] public section

namespace Unfoldings

/-- A connected curve with two closed possible lifts has one fixed branch. Separation is
needed only at the curve's actual parameters, so the branches may merge elsewhere. -/
theorem exists_fixed_bool_lift {A T X : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    [TopologicalSpace X] (curve : A → X) (continuous_curve : Continuous curve)
    (bank : Bool → T → X) (closed : ∀ b, IsClosed (Set.range (bank b))) (time : A → T)
    (copies : ∀ a, ∃ b, curve a = bank b (time a))
    (separated : ∀ a b c, b ≠ c → ∀ t, bank b (time a) ≠ bank c t) :
    ∃ b, ∀ a, curve a = bank b (time a) := by
  let S (b : Bool) : Set A := curve ⁻¹' Set.range (bank b)
  have closed_S (b : Bool) : IsClosed (S b) := (closed b).preimage continuous_curve
  have exact_copy (a : A) (b : Bool) (member : a ∈ S b) : curve a = bank b (time a) := by
    obtain ⟨c, copy⟩ := copies a
    obtain ⟨t, at_t⟩ := member
    by_cases same : c = b
    · exact same ▸ copy
    · exact (separated a c b same t (copy.symm.trans at_t.symm)).elim
  have cover : Set.univ ⊆ S false ∪ S true := by
    intro a _
    obtain ⟨b, copy⟩ := copies a
    cases b
    · exact Or.inl ⟨time a, copy.symm⟩
    · exact Or.inr ⟨time a, copy.symm⟩
  have disjoint : Disjoint (S false) (S true) := by
    apply Set.disjoint_left.mpr
    intro a first last
    exact separated a false true (by decide) (time a)
      ((exact_copy a false first).symm.trans (exact_copy a true last))
  have fixed : ∃ b, ∀ a, a ∈ S b := by
    by_cases first : (S false).Nonempty
    · refine ⟨false, fun a => ?_⟩
      rcases cover (Set.mem_univ a) with member | member
      · exact member
      · obtain ⟨b, hb⟩ := first
        obtain ⟨c, _, left, right⟩ := isPreconnected_closed_iff.mp isPreconnected_univ
          (S false) (S true) (closed_S false) (closed_S true) cover
          ⟨b, Set.mem_univ b, hb⟩ ⟨a, Set.mem_univ a, member⟩
        exact (Set.disjoint_left.mp disjoint left right).elim
    · refine ⟨true, fun a => ?_⟩
      rcases cover (Set.mem_univ a) with member | member
      · exact (first ⟨a, member⟩).elim
      · exact member
  obtain ⟨b, all⟩ := fixed
  exact ⟨b, fun a => exact_copy a b (all a)⟩

end Unfoldings
