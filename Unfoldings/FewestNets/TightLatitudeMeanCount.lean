module

public import Unfoldings.FewestNets.RevisedLatitudeMeanCount
public import Unfoldings.FewestNets.TightLatitudeAnalyticCount
public import Unfoldings.FewestNets.CheckedLatitudeCoefficient

/-! The refined count uses the same orthogonal-placement measure for every selector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real
open AcuteLatitudeGrid (tightAnalyticPrefactorScale tightAnalyticPrefactorScale_pos)

/-- The annular allowance uses the analytic estimate through 0.42 and the exact
algebraic charge on the certified interval range. -/
def tightSelectorCountAllowance {a : ℝ} (key : Selector a) : ℝ :=
  key.elim (fun _ => 2.45 / a ^ 2) (fun i =>
    if a ≤ 0.42 then (tightAnalyticPrefactorScale a / a) * analyticAnnularCharge i
    else tightAnnularPrefactor a * annularAlgebraicCharge i)

theorem tightSelectorCountAllowance_sum_lt {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (interval_bound : 0.42 < a → normalizedGridCoefficient a < 246.3) :
    2 + (∑ key : Selector a, tightSelectorCountAllowance key) < 246.3 / a ^ 4 := by
  rw [Fintype.sum_sum_type]
  simp only [tightSelectorCountAllowance, Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  by_cases low : a ≤ 0.42
  · simp only [if_pos low]
    rw [← Finset.mul_sum]
    convert analyticAnnularCharge_sum_lt positive small low using 1
    ring
  · simp only [if_neg low]
    rw [← Finset.mul_sum, ← gridCharge_eq_sum positive small]
    apply (lt_div_iff₀ (pow_pos positive 4)).mpr
    convert interval_bound (lt_of_not_ge low) using 1
    unfold normalizedGridCoefficient
    field_simp [positive.ne']
    <;> ring

end Unfoldings.FewestNets.RevisedLatitudeGrid

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets RevisedLatitudeGrid SphericalSelectorBoundary SpatialRotation MeasureTheory
  InnerProductGeometry Real
open AcuteLatitudeGrid (input_cornerAngle_lower local_count_prefactor_tight tightAnalyticPrefactorScale
  tightAnalyticPrefactorScale_pos)

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)
  {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

include P in
/-- The mean number of components selected by each actual grid region. -/
theorem mean_tightLatitudeSelectedCount_le
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ π / 2 - a) (key : Selector a) :
    let region := selectorSphere positive small key
    ((∫ g, gaussianSelectedCount N region false g ∂probability) +
      (∫ g, gaussianSelectedCount N region true g ∂probability)) / 2 ≤
      2 * uniformSphere.real region + tightSelectorCountAllowance key := by
  rcases key with pole | i
  · exact P.mean_revisedLatitudeSelectedCount_le N positive small angles (.inl pole)
  · let M := tightAnnularSelectorMetric positive small i
    have eta_pos : 0 < 2 * a := by positivity
    have eta_small : 2 * a ≤ π / 2 := by linarith only [small, pi_pos]
    have minimum (f : Face) (j : Fin 3) : 2 * a ≤ (C.triangle f).cornerAngle j :=
      input_cornerAngle_lower (C.triangle f) (angles f) j
    obtain ⟨q, unit, hemisphere⟩ := exists_selectorSphere_hemisphere positive small (.inr i)
    have count := P.mean_gaussianSelectedCount_le N M q unit hemisphere eta_pos eta_small minimum
    have budget_nonneg : 0 ≤ M.crossingBudget :=
      (div_nonneg (Finset.sum_nonneg (fun j _ => (M.endpointFactor_pos j.1 j.2).le)) pi_pos.le).trans
        (le_max_left _ _)
    change _ ≤ _ + (if a ≤ 0.42 then (tightAnalyticPrefactorScale a / a) * analyticAnnularCharge i
      else tightAnnularPrefactor a * annularAlgebraicCharge i)
    by_cases low : a ≤ 0.42
    · rw [if_pos low]
      have coefficient := local_count_prefactor_tight positive low M.separation_pos.le M.separation_small
      exact count.trans (add_le_add le_rfl (mul_le_mul coefficient.le
        (tightAnnularSelectorMetric_crossingBudget_le positive small low i) budget_nonneg (div_nonneg (tightAnalyticPrefactorScale_pos a).le positive.le)))
    · rw [if_neg low]
      have pp : 0 ≤ tightAnnularPrefactor a := by
        unfold tightAnnularPrefactor
        have sn := sin_nonneg_of_nonneg_of_le_pi eta_pos.le (eta_small.trans (by linarith only [pi_pos]))
        positivity
      exact count.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (tightAnnularSelectorMetric_crossingBudget_le_algebraic positive small i) pp))

end Unfoldings.SpatialFolding.ConvexBoundary
