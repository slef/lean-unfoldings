module

public import Unfoldings.FewestNets.AcuteLatitudeRows
public import Unfoldings.FewestNets.SelectedCellAveraging

/-! Numeric budgets for the current acute latitude construction and the strict 1440 bound. -/

@[expose] public section

namespace Unfoldings.FewestNets

open Real MeasureTheory

/-- Sum the area term, the two polar excesses, and all annular excesses. -/
theorem acute_latitude_component_bound {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    2 + 17.02 / a ^ 2 + (476 / a ^ 2) * (3 / a ^ 2) < 1440 / a ^ 4 := by
  have a_le : a ≤ 2 / 3 := by linarith only [small, pi_lt_d4]
  have sq : a ^ 2 ≤ (2 / 3 : ℝ) ^ 2 := pow_le_pow_left₀ positive.le a_le 2
  have fourth : a ^ 4 ≤ (2 / 3 : ℝ) ^ 4 := pow_le_pow_left₀ positive.le a_le 4
  apply (lt_div_iff₀ (pow_pos positive 4)).mpr
  calc
    _ = 2 * a ^ 4 + 17.02 * a ^ 2 + 476 * 3 := by field_simp [positive.ne']
    _ < _ := by linarith only [sq, fourth]

/-- The wider cells leave the required projection and bank-opening margins. -/
theorem acute_latitude_cone_budget {a φ Ω : ℝ} (positive : 0 < a)
    (tilt : φ ^ 2 < 0.0335 * a) (curvature : Ω < 0.0163 * a) :
    0.504 * φ ^ 2 < 0.018 * a ∧ 3.008 * φ ^ 2 + 4 * Ω < 0.170 * a := by
  constructor <;> linarith only [positive, tilt, curvature]

/-- The signed east and west sides leave the required angular margin at all three exits. -/
theorem acute_latitude_exit_budget {a east west : ℝ} (positive : 0 < a)
    (east_bound : |east| ≤ 0.641 * a) (west_bound : |west| ≤ 0.641 * a)
    (apex : west - east ≤ 0.641 * a) :
    0.170 * a < min (0.491 * a + east / 2)
      (min (0.491 * a - west / 2) (2 * 0.491 * a + east - west)) := by
  refine lt_min ?_ (lt_min ?_ ?_)
  · linarith only [positive, (abs_le.mp east_bound).1]
  · linarith only [positive, (abs_le.mp west_bound).2]
  · linarith only [positive, apex]

/-- Assemble the current numerical bound from the actual cell excesses
and original-edge developments. -/
theorem exists_acute_latitude_net_partition_of_expected_selected_counts
    {Face Rotation : Type*} [Fintype Face] [MeasurableSpace Rotation]
    (C : TriangleComplex Face) (μ : Measure Rotation) [IsProbabilityMeasure μ]
    {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (label : Rotation → Face → (Fin 2 ⊕ Fin (AcuteLatitudeGrid.triangleCount a)))
    (bad : Set Rotation) (null : μ bad = 0)
    (mass : Fin 2 ⊕ Fin (AcuteLatitudeGrid.triangleCount a) → ℝ) (total : ∑ i, mass i = 1)
    (integrable : ∀ i, Integrable (selectedCount C label i) μ)
    (expected : ∀ i, (∫ r, selectedCount C label i r ∂μ) ≤ 2 * mass i +
      Sum.elim (fun _ : Fin 2 => 8.51 / a ^ 2) (fun _ : Fin (AcuteLatitudeGrid.triangleCount a) => 3 / a ^ 2) i)
    (net : ∀ r ∉ bad, ∀ c : (C.labeledSeamGraph (label r)).ConnectedComponent,
      C.HasOriginalEdgeNet c.supp) :
    ∃ n : ℕ, (n : ℝ) < 1440 / a ^ 4 ∧ C.HasNetPartition n := by
  obtain ⟨n, bound, hnet⟩ := exists_net_partition_of_expected_selected_counts
    C μ label bad null mass _ total integrable expected net
  have sum :
      (∑ i : Fin 2 ⊕ Fin (AcuteLatitudeGrid.triangleCount a),
        Sum.elim (fun _ => 8.51 / a ^ 2) (fun _ => 3 / a ^ 2) i) =
        17.02 / a ^ 2 + (AcuteLatitudeGrid.triangleCount a : ℝ) * (3 / a ^ 2) := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [sum] at bound
  have scaled := mul_le_mul_of_nonneg_right (AcuteLatitudeGrid.triangleCount_lt positive small).le
    (by positivity : 0 ≤ 3 / a ^ 2)
  exact ⟨n, by linarith only [bound, scaled, acute_latitude_component_bound positive small], hnet⟩

end Unfoldings.FewestNets
