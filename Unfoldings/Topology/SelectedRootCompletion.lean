module

public import Unfoldings.Topology.SelectedForest

/-! Connect unused parent roots without changing any of the already selected edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents.EdgeSelection

variable {V E : Type*} {P : AscendingParents V} {G : Graph V E} (S : P.EdgeSelection G)

/-- A completion keeps the potential and every old nonroot parent and selected edge. -/
structure RootCompletion (roots : Set V) where
  parents : AscendingParents V
  roots_eq : parents.roots = roots
  height_eq : parents.height = P.height
  parent_eq : ∀ v ∉ P.roots, parents.parent v = P.parent v
  selection : parents.EdgeSelection G
  selected_subset : Set.range S.edge ⊆ Set.range selection.edge

/-- Only the unwanted old roots need additional increasing neighbors. -/
def completeRoots (roots : Set V) (subset : roots ⊆ P.roots)
    (progress : ∀ v ∈ P.roots, v ∉ roots → ∃ w e,
      G.IsLink e v w ∧ P.height v < P.height w) : S.RootCompletion roots := by
  classical
  let nextVertex (v : V) := if old : v ∈ P.roots then
    if root : v ∈ roots then v else (progress v old root).choose
    else P.parent v
  let Q : AscendingParents V :=
    { roots := roots
      parent := nextVertex
      height := P.height
      fixed_root := fun v root => by
        simp only [nextVertex, dite_eq_left (subset root), dite_eq_left root]
      ascending := fun v nonroot => by
        by_cases old : v ∈ P.roots
        · simp only [nextVertex, dite_eq_left old, dite_eq_right nonroot]
          exact (progress v old nonroot).choose_spec.choose_spec.2
        · simp only [nextVertex, dite_eq_right old]
          exact P.ascending v old }
  let T : Q.EdgeSelection G :=
    { edge := fun v => if old : v.val ∈ P.roots then
        (progress v.val old v.property).choose_spec.choose else S.edge ⟨v.val, old⟩
      link := fun v => by
        have nonroot : v.val ∉ roots := v.property
        change G.IsLink _ v.val (nextVertex v.val)
        by_cases old : v.val ∈ P.roots
        · simp only [dite_eq_left old, nextVertex, dite_eq_right nonroot]
          exact (progress v.val old nonroot).choose_spec.choose_spec.1
        · simp only [dite_eq_right old, nextVertex]
          exact S.link ⟨v.val, old⟩ }
  refine ⟨Q, rfl, rfl, ?_, T, ?_⟩
  · intro v nonroot
    change nextVertex v = P.parent v
    simp only [nextVertex, dite_eq_right nonroot]
  · rintro e ⟨v, rfl⟩
    have nonroot : v.val ∉ Q.roots := fun root => v.property (subset root)
    refine ⟨⟨v.val, nonroot⟩, ?_⟩
    change (if old : v.val ∈ P.roots then _ else _) = S.edge v
    simp only [dite_eq_right v.property]

end Unfoldings.AscendingParents.EdgeSelection
