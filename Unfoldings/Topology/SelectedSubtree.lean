module

public import Unfoldings.Topology.SelectedForest
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Descendant subtrees of selected forests

A nonroot's descendants contain no roots. Its own original named parent edge
is the unique selected edge leaving them. Counting its internal edge ends and
this one exit gives twice the vertex count minus one.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents

variable {V : Type*} (P : AscendingParents V)

/-- A root cannot be a descendant of a nonroot. -/
theorem descendant_nonroot {v e : V} (nonroot : e ∉ P.roots)
    (descendant : P.Ancestor v e) : v ∉ P.roots := by
  intro root
  obtain ⟨n, reaches⟩ := descendant
  have same : v = e := (Function.iterate_fixed (P.fixed_root v root) n).symm.trans reaches
  exact nonroot (same ▸ root)

/-- The only descendant whose parent leaves the subtree is its top vertex. -/
theorem ancestor_parent_iff_descendant_ne {e v : V} (nonroot : e ∉ P.roots) :
    P.Ancestor (P.parent v) e ↔ P.Ancestor v e ∧ v ≠ e := by
  constructor
  · intro reaches
    refine ⟨(P.ancestor_parent v).trans P reaches, ?_⟩
    rintro rfl
    exact P.not_ancestor_parent_self nonroot reaches
  · rintro ⟨reaches, different⟩
    exact (P.ancestor_parent_iff different).mp reaches

variable [Fintype V]

/-- The actual finite descendant set, including the top vertex. -/
def descendants (e : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => P.Ancestor v e)

@[simp] theorem mem_descendants (v e : V) : v ∈ P.descendants e ↔ P.Ancestor v e := by
  classical
  simp only [descendants, Finset.mem_filter, Finset.mem_univ, true_and]

open scoped Classical in
/-- Count selected edge ends lying in a nonroot descendant subtree. -/
theorem sum_descendant_incidence (e : V) (nonroot : e ∉ P.roots) :
    (∑ v : V, ((if P.Ancestor v e then (1 : ℝ) else 0) +
      (if P.Ancestor (P.parent v) e then (1 : ℝ) else 0))) =
        2 * (P.descendants e).card - 1 := by
  classical
  have top : e ∈ P.descendants e := (P.mem_descendants e e).mpr (P.ancestor_refl e)
  have parents : Finset.univ.filter (fun v => P.Ancestor (P.parent v) e) =
      (P.descendants e).erase e := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      P.mem_descendants, P.ancestor_parent_iff_descendant_ne nonroot]
    exact and_comm
  have first : (∑ v : V, if P.Ancestor v e then (1 : ℝ) else 0) =
      (P.descendants e).card := by
    simp only [descendants, Finset.sum_boole]
  have second : (∑ v : V, if P.Ancestor (P.parent v) e then (1 : ℝ) else 0) =
      (P.descendants e).card - 1 := by
    rw [Finset.sum_boole, parents, Finset.card_erase_of_mem top,
      Nat.cast_sub (Finset.card_pos.mpr ⟨e, top⟩), Nat.cast_one]
  rw [Finset.sum_add_distrib, first, second]
  ring

end Unfoldings.AscendingParents

namespace Unfoldings.AscendingParents.EdgeSelection

variable {V E : Type*} {P : AscendingParents V} {G : Graph V E} (S : P.EdgeSelection G)

/-- The parent edge is exactly the selected edge crossing the descendant separator. -/
theorem crosses_descendants_iff {e a b : V} (nonroot : e ∉ P.roots) {edge : E}
    (link : S.graph.IsLink edge a b) :
    ((P.Ancestor a e ∧ ¬ P.Ancestor b e) ∨
      (P.Ancestor b e ∧ ¬ P.Ancestor a e)) ↔ edge = S.edge ⟨e, nonroot⟩ := by
  obtain ⟨w, named, endpoints⟩ := link
  have different (unequal : w.val ≠ e) :
      ¬ ((P.Ancestor w.val e ∧ ¬ P.Ancestor (P.parent w.val) e) ∨
        (P.Ancestor (P.parent w.val) e ∧ ¬ P.Ancestor w.val e)) := by
    have same := P.ancestor_parent_iff unequal
    rintro (⟨inside, outside⟩ | ⟨inside, outside⟩)
    · exact outside (same.mp inside)
    · exact outside (same.mpr inside)
  have top : P.Ancestor e e ∧ ¬ P.Ancestor (P.parent e) e :=
    ⟨P.ancestor_refl e, P.not_ancestor_parent_self nonroot⟩
  constructor
  · intro crossing
    have same : w.val = e := by
      by_contra unequal
      apply different unequal
      rcases endpoints with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact crossing
      · exact crossing.elim Or.inr Or.inl
    have vertices : w = ⟨e, nonroot⟩ := Subtype.ext same
    exact named.symm.trans (congrArg S.edge vertices)
  · intro equal
    have same : w = ⟨e, nonroot⟩ := S.edge_injective (named.trans equal)
    subst w
    rcases endpoints with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl top
    · exact Or.inr top

end Unfoldings.AscendingParents.EdgeSelection
