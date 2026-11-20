module

public import Unfoldings.Topology.FinitePathRange
public import Mathlib.Analysis.Convex.Contractible

/-! A finite chain of interval fibers is again one interval. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {X : Type*} [TopologicalSpace X]

/-- Concatenation preserves injectivity when two arcs meet only at their common endpoint. -/
theorem Path.injective_trans_of_inter_subset {x y z : X} (a : Path x y) (b : Path y z)
    (injective_a : Function.Injective a) (injective_b : Function.Injective b)
    (meet : Set.range a ∩ Set.range b ⊆ {y}) : Function.Injective (a.trans b) := by
  intro s t eq
  have at_joint (u v : unitInterval) (same : a u = b v) : u = 1 ∧ v = 0 := by
    have end_at : a u = y := meet ⟨Set.mem_range_self u, ⟨v, same.symm⟩⟩
    exact ⟨injective_a (end_at.trans a.target.symm),
      injective_b (same.symm.trans (end_at.trans b.source.symm))⟩
  rw [Path.trans_apply, Path.trans_apply] at eq
  apply Subtype.ext
  split_ifs at eq with hs ht ht
  · have named := congrArg Subtype.val (injective_a eq)
    change 2 * s.val = 2 * t.val at named
    linarith
  · obtain ⟨_, zero⟩ := at_joint _ _ eq
    have named := congrArg Subtype.val zero
    change 2 * t.val - 1 = 0 at named
    linarith
  · obtain ⟨_, zero⟩ := at_joint _ _ eq.symm
    have named := congrArg Subtype.val zero
    change 2 * s.val - 1 = 0 at named
    linarith
  · have named := congrArg Subtype.val (injective_b eq)
    change 2 * s.val - 1 = 2 * t.val - 1 at named
    linarith

/-- A nonempty finite list of arcs with only the stated consecutive contacts
parametrizes their entire union by an injective path. -/
theorem exists_injective_path_eq_iUnion_arcs {n : ℕ} (vertex : Fin (n + 2) → X)
    (arc : ∀ i : Fin (n + 1), Path (vertex i.castSucc) (vertex i.succ))
    (injective : ∀ i, Function.Injective (arc i))
    (meet : ∀ i j : Fin (n + 1), i < j →
      Set.range (arc i) ∩ Set.range (arc j) ⊆ {vertex j.castSucc}) :
    ∃ P : Path (vertex 0) (vertex (Fin.last (n + 1))),
      Function.Injective P ∧ Set.range P = ⋃ i, Set.range (arc i) := by
  induction n with
  | zero =>
    refine ⟨arc 0, injective 0, Set.Subset.antisymm ?_ ?_⟩
    · intro x hx
      exact Set.mem_iUnion.mpr ⟨0, hx⟩
    · intro x member
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
      have same : i = 0 := by
        apply Fin.ext
        change i.val = 0
        have hi_lt : i.val < 1 := i.isLt
        omega
      rw [same] at hi
      exact hi
  | succ n ih =>
    let V := vertex ∘ Fin.castSucc
    let A (i : Fin (n + 1)) : Path (V i.castSucc) (V i.succ) := arc i.castSucc
    obtain ⟨P, inj, range_eq⟩ := ih V A (fun i => injective i.castSucc)
      (fun i j h => meet i.castSucc j.castSucc ((Fin.castSucc_lt_castSucc_iff ..).mpr h))
    let Q := arc (Fin.last (n + 1))
    have join : Set.range P ∩ Set.range Q ⊆ {vertex (Fin.last (n + 1)).castSucc} := by
      rintro x ⟨on_P, on_Q⟩
      rw [range_eq] at on_P
      obtain ⟨i, on_arc⟩ := Set.mem_iUnion.mp on_P
      exact meet i.castSucc (Fin.last (n + 1)) (Fin.castSucc_lt_last i) ⟨on_arc, on_Q⟩
    have exact_range : Set.range (P.trans Q) = ⋃ i, Set.range (arc i) := by
      rw [Path.trans_range, range_eq]
      ext x
      simp only [Set.mem_union, Set.mem_iUnion]
      constructor
      · rintro (⟨i, hi⟩ | h)
        · exact ⟨i.castSucc, hi⟩
        · exact ⟨Fin.last (n + 1), h⟩
      · rintro ⟨i, hi⟩
        revert hi
        refine Fin.lastCases ?_ (fun j => ?_) i
        · exact Or.inr
        · exact fun h => Or.inl ⟨j, h⟩
    exact ⟨P.trans Q, Unfoldings.Path.injective_trans_of_inter_subset P Q inj
      (injective (Fin.last (n + 1))) join, exact_range⟩

/-- A finite chain of actual arcs has contractible union in a Hausdorff space. -/
theorem contractibleSpace_iUnion_arcs [T2Space X] {n : ℕ} (vertex : Fin (n + 2) → X)
    (arc : ∀ i : Fin (n + 1), Path (vertex i.castSucc) (vertex i.succ))
    (injective : ∀ i, Function.Injective (arc i))
    (meet : ∀ i j : Fin (n + 1), i < j →
      Set.range (arc i) ∩ Set.range (arc j) ⊆ {vertex j.castSucc}) :
    ContractibleSpace (⋃ i, Set.range (arc i)) := by
  obtain ⟨P, injective, range_eq⟩ := exists_injective_path_eq_iUnion_arcs vertex arc injective meet
  rw [← range_eq]
  let q (t : unitInterval) : Set.range P := ⟨P t, Set.mem_range_self t⟩
  have bijective : Function.Bijective q :=
    ⟨fun _ _ eq => injective (congrArg Subtype.val eq), fun ⟨_, t, ht⟩ => ⟨t, Subtype.ext ht⟩⟩
  let H := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective q bijective)
    (P.continuous.subtype_mk _)
  let : ContractibleSpace unitInterval := (convex_Icc (0 : ℝ) 1).contractibleSpace
    ⟨0, le_rfl, zero_le_one⟩
  exact H.symm.contractibleSpace

/-- A finite chain includes its named vertices. In particular, a chain with
no arcs is its single initial vertex. -/
theorem contractibleSpace_vertices_union_arcs [T2Space X] {n : ℕ} (vertex : Fin (n + 1) → X)
    (arc : ∀ i : Fin n, Path (vertex i.castSucc) (vertex i.succ))
    (injective : ∀ i, Function.Injective (arc i))
    (meet : ∀ i j : Fin n, i < j →
      Set.range (arc i) ∩ Set.range (arc j) ⊆ {vertex j.castSucc}) :
    ContractibleSpace ↥(Set.range vertex ∪ (⋃ i, Set.range (arc i))) := by
  cases n with
  | zero =>
    have singleton : Set.range vertex ∪ (⋃ i, Set.range (arc i)) = {vertex 0} := by
      ext x
      constructor
      · rintro (⟨i, rfl⟩ | member)
        · have hi : i = 0 := by
            apply Fin.ext
            change i.val = 0
            have bound : i.val < 1 := i.isLt
            omega
          exact Set.mem_singleton_iff.mpr (congrArg vertex hi)
        · obtain ⟨i, _⟩ := Set.mem_iUnion.mp member
          exact Fin.elim0 i
      · intro member
        exact Or.inl ⟨0, (Set.mem_singleton_iff.mp member).symm⟩
    rw [singleton]
    infer_instance
  | succ n =>
    have contains : Set.range vertex ⊆ ⋃ i, Set.range (arc i) := by
      rintro _ ⟨i, rfl⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact Set.mem_iUnion.mpr ⟨Fin.last n, 1, (arc (Fin.last n)).target⟩
      · exact Set.mem_iUnion.mpr ⟨j, 0, (arc j).source⟩
    rw [Set.union_eq_right.mpr contains]
    exact contractibleSpace_iUnion_arcs vertex arc injective meet

end Unfoldings
