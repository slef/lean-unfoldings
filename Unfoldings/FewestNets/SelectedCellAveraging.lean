module

public import Unfoldings.FewestNets.ComponentAveraging
public import Unfoldings.Polyhedron.LabeledSelectionCount

/-! Assemble independently counted selectors into one original-edge net partition. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeasureTheory Real

variable {Face Rotation Label : Type*} [Fintype Face] [Fintype Label] [MeasurableSpace Rotation]
  (C : TriangleComplex Face) (μ : Measure Rotation) [IsProbabilityMeasure μ]
  (label : Rotation → Face → Label)

/-- Count the same-label original face components belonging to a specified cell. -/
def selectedCount (i : Label) (r : Rotation) : ℝ :=
  Nat.card (C.SelectedComponents {f | label r f = i})

/-- The sum of cell-area marginals is one, so only the cell excesses above
twice their marginals contribute to the expected component bound. -/
theorem exists_net_partition_of_expected_selected_counts (bad : Set Rotation) (null : μ bad = 0)
    (mass bound : Label → ℝ)
    (total : ∑ i, mass i = 1)
    (integrable : ∀ i, Integrable (selectedCount C label i) μ)
    (expected : ∀ i, (∫ r, selectedCount C label i r ∂μ) ≤ 2 * mass i + bound i)
    (net : ∀ r ∉ bad, ∀ c : (C.labeledSeamGraph (label r)).ConnectedComponent,
      C.HasOriginalEdgeNet c.supp) :
    ∃ n : ℕ, (n : ℝ) ≤ 2 + ∑ i, bound i ∧ C.HasNetPartition n := by
  let charge (i : Label) (r : Rotation) := selectedCount C label i r - 2 * mass i
  have finite (i : Label) : Integrable (charge i) μ :=
    (integrable i).sub (integrable_const _)
  apply exists_net_partition_of_expected_component_charges C μ bad null label charge finite bound _ _ net
  · intro i
    unfold charge
    rw [integral_sub (integrable i) (integrable_const _), integral_const,
      probReal_univ, one_smul]
    linarith only [expected i]
  · intro r _
    rw [show (Nat.card (C.labeledSeamGraph (label r)).ConnectedComponent : ℝ) =
        ∑ i, selectedCount C label i r by
          have eq := congrArg (fun n : ℕ => (n : ℝ))
            (C.card_labeledComponents_eq_sum_selectedComponents (label r))
          rw [Nat.cast_sum] at eq
          exact eq]
    simp only [charge, Finset.sum_sub_distrib, ← Finset.mul_sum, total]
    ring

end Unfoldings.FewestNets
