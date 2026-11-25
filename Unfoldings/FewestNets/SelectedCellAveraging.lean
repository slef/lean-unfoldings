module

public import Unfoldings.FewestNets.ComponentAveraging
public import Unfoldings.FewestNets.LatitudeCount
public import Unfoldings.FewestNets.LatitudeRows
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

/-- The explicit numerical assembly step once the latitude selectors have
their local original-edge nets and the two kinds of cell-excess estimates. -/
theorem exists_latitude_net_partition_of_expected_selected_counts
    {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (label : Rotation → Face → (Fin 2 ⊕ Fin (latitudeTriangleCount a)))
    (bad : Set Rotation) (null : μ bad = 0)
    (mass : Fin 2 ⊕ Fin (latitudeTriangleCount a) → ℝ)
    (total : ∑ i, mass i = 1)
    (integrable : ∀ i, Integrable (selectedCount C label i) μ)
    (expected : ∀ i, (∫ r, selectedCount C label i r ∂μ) ≤ 2 * mass i +
      Sum.elim (fun _ : Fin 2 => 36 / a ^ 2)
        (fun _ : Fin (latitudeTriangleCount a) => 5.6475 / a ^ 2) i)
    (net : ∀ r ∉ bad, ∀ c : (C.labeledSeamGraph (label r)).ConnectedComponent,
      C.HasOriginalEdgeNet c.supp) :
    ∃ n : ℕ, (n : ℝ) < 13000 / a ^ 4 ∧ C.HasNetPartition n := by
  obtain ⟨n, bound, net⟩ := exists_net_partition_of_expected_selected_counts
    C μ label bad null mass _ total integrable expected net
  have sum :
      (∑ i : Fin 2 ⊕ Fin (latitudeTriangleCount a),
        Sum.elim (fun _ => 36 / a ^ 2) (fun _ => 5.6475 / a ^ 2) i) =
        72 / a ^ 2 + (latitudeTriangleCount a : ℝ) * (5.6475 / a ^ 2) := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [sum] at bound
  have triangles := mul_le_mul_of_nonneg_right (latitudeTriangleCount_lt positive small).le
    (by positivity : 0 ≤ 5.6475 / a ^ 2)
  have entire := latitude_component_bound positive small
  exact ⟨n, by linarith only [bound, triangles, entire], net⟩

end Unfoldings.FewestNets
