module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

/-! Consecutive marked points in a finite subdivision of a real interval. -/

@[expose] public section

namespace Unfoldings

theorem marked_gap_unique {T : Set ℝ} {a b c d x : ℝ}
    (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hd : d ∈ T)
    (first : Disjoint T (Set.Ioo a b)) (second : Disjoint T (Set.Ioo c d))
    (hx : x ∈ Set.Ioo a b) (hy : x ∈ Set.Ioo c d) : a = c ∧ b = d := by
  have left : a = c := by
    rcases lt_trichotomy a c with h | equal | h
    · exact (Set.disjoint_left.mp first hc ⟨h, hy.1.trans hx.2⟩).elim
    · exact equal
    · exact (Set.disjoint_left.mp second ha ⟨h, hx.1.trans hy.2⟩).elim
  have right : b = d := by
    rcases lt_trichotomy b d with h | equal | h
    · exact (Set.disjoint_left.mp second hb ⟨hy.1.trans hx.2, h⟩).elim
    · exact equal
    · exact (Set.disjoint_left.mp first hd ⟨hx.1.trans hy.2, h⟩).elim
  exact ⟨left, right⟩

theorem exists_marked_gap {T : Set ℝ} (finite : T.Finite) {a b x : ℝ}
    (ha : a ∈ T) (hb : b ∈ T) (hx : x ∈ Set.Icc a b) (unmarked : x ∉ T) :
    ∃ u ∈ T, ∃ v ∈ T, a ≤ u ∧ u < x ∧ x < v ∧ v ≤ b ∧ Disjoint T (Set.Ioo u v) := by
  let lower := {t ∈ T | a ≤ t ∧ t ≤ x}
  let upper := {t ∈ T | x ≤ t ∧ t ≤ b}
  have compact_lower : IsCompact lower := (finite.subset (fun _ h => h.1)).isCompact
  have compact_upper : IsCompact upper := (finite.subset (fun _ h => h.1)).isCompact
  obtain ⟨u, hu, greatest⟩ := compact_lower.exists_isMaxOn ⟨a, ha, le_rfl, hx.1⟩
    continuous_id.continuousOn
  obtain ⟨v, hv, least⟩ := compact_upper.exists_isMinOn ⟨b, hb, hx.2, le_rfl⟩
    continuous_id.continuousOn
  have before : u < x := lt_of_le_of_ne hu.2.2 (fun equal => unmarked (equal ▸ hu.1))
  have after : x < v := lt_of_le_of_ne hv.2.1 (fun equal => unmarked (equal.symm ▸ hv.1))
  refine ⟨u, hu.1, v, hv.1, hu.2.1, before, after, hv.2.2, Set.disjoint_left.mpr ?_⟩
  intro t ht between
  by_cases side : t ≤ x
  · have bound := greatest (show t ∈ lower from ⟨ht, hu.2.1.trans between.1.le, side⟩)
    exact (not_lt_of_ge bound between.1)
  · have bound := least (show t ∈ upper from
      ⟨ht, (le_of_not_ge side), between.2.le.trans hv.2.2⟩)
    exact (not_lt_of_ge bound between.2)

theorem marked_unordered_gap_unique {T : Set ℝ} {a b c d x : ℝ}
    (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hd : d ∈ T)
    (first : Disjoint T (Set.Ioo (min a b) (max a b)))
    (second : Disjoint T (Set.Ioo (min c d) (max c d)))
    (hx : x ∈ Set.Ioo (min a b) (max a b))
    (hy : x ∈ Set.Ioo (min c d) (max c d)) : Set.uIcc a b = Set.uIcc c d := by
  have mem_min {r s : ℝ} (hr : r ∈ T) (hs : s ∈ T) : min r s ∈ T :=
    (min_choice r s).elim (fun equal => equal.symm ▸ hr) (fun equal => equal.symm ▸ hs)
  have mem_max {r s : ℝ} (hr : r ∈ T) (hs : s ∈ T) : max r s ∈ T :=
    (max_choice r s).elim (fun equal => equal.symm ▸ hr) (fun equal => equal.symm ▸ hs)
  obtain ⟨left, right⟩ := marked_gap_unique (mem_min ha hb) (mem_max ha hb)
    (mem_min hc hd) (mem_max hc hd) first second hx hy
  exact congrArg₂ Set.Icc left right

end Unfoldings
