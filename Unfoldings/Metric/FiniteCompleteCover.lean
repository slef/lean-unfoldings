module

public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.UniformSpace.CompleteSeparated
public import Mathlib.Data.Finset.Lattice.Fold

/-! A finite isometric cover by complete spaces makes the entire extended metric space complete. -/

@[expose] public section

noncomputable section

namespace Unfoldings

universe u v w

theorem completeSpace_of_finite_isometric_cover {I : Type u} [Finite I]
    {X : Type v} [EMetricSpace X] (E : I → Type w)
    [∀ i, EMetricSpace (E i)] [∀ i, CompleteSpace (E i)]
    (maps : ∀ i, E i → X) (isometric : ∀ i, Isometry (maps i))
    (cover : ∀ x, ∃ i, ∃ p, maps i p = x) : CompleteSpace X := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have pieces (i : I) : IsComplete (Set.range (maps i)) :=
    (isometric i).isUniformInducing.isComplete_range
  have finite_union (t : Finset I) : IsComplete (t.sup (fun i => Set.range (maps i))) := by
    induction t using Finset.induction_on with
    | empty => exact isCompact_empty.isComplete
    | @insert i t _ ih =>
      rw [Finset.sup_insert]
      exact (pieces i).union ih
  apply completeSpace_iff_isComplete_univ.mpr
  have all : Finset.univ.sup (fun i => Set.range (maps i)) = Set.univ := by
    rw [Finset.sup_eq_iSup]
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, p, equal⟩ := cover x
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ i, ⟨p, equal⟩⟩⟩
  rw [← all]
  exact finite_union Finset.univ

end Unfoldings
