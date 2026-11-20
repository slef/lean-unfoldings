module

public import Unfoldings.FewestNets.ComponentAveraging
public import Unfoldings.FewestNets.CountConstants
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-! The area-weighted count obtained from the two spherical side-length
estimates and the localized and unlocalized crossing estimates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real MeasureTheory
open scoped BigOperators

private theorem cos_div_two_pos {x : ℝ} (hx : 0 ≤ x) (h : x ≤ 1) :
    0 < cos (x / 2) :=
  cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_gt_three]⟩

/-- The denominator of the small-diameter perimeter estimate increases through diameter one. -/
theorem monotoneOn_diameter_mul_cos_sq :
    MonotoneOn (fun d : ℝ => d * cos (d / 2) ^ 2) (Set.Icc 0 1) := by
  have derivative (d : ℝ) :
      HasDerivAt (fun x : ℝ => x * cos (x / 2) ^ 2)
        (cos (d / 2) * (cos (d / 2) - d * sin (d / 2))) d := by
    have half := (hasDerivAt_id d).div_const (2 : ℝ)
    have h := (hasDerivAt_id d).mul (half.cos.pow 2)
    convert h using 1 <;> first | rfl | (simp [id]; ring)
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · have half : Continuous (fun x : ℝ => x / 2) := continuous_id.div_const _
    exact (continuous_id.mul ((continuous_cos.comp half).pow 2)).continuousOn
  · intro x _
    exact (derivative x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(derivative x).deriv]
    have hx_sq : (x / 2) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by linarith [hx.1]) (by linarith [hx.2]) 2
    have cos_bound := one_sub_sq_div_two_le_cos (x := x / 2)
    have sin_bound := Real.sin_le (show 0 ≤ x / 2 by linarith [hx.1])
    have product : x * sin (x / 2) ≤ x / 2 :=
      (mul_le_mul_of_nonneg_left sin_bound hx.1.le).trans (by
        nlinarith [mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le)])
    exact mul_nonneg (cos_div_two_pos hx.1.le hx.2.le).le (by linarith [hx.2])

/-- For a polygon at least as wide as the separation scale, the two spherical
area estimates give a common bound on the residual perimeter. -/
theorem residualPerimeter_le_of_separation {s d S A t : ℝ}
    (s_positive : 0 < s) (s_small : s ≤ 1 / 2) (separation : s ≤ d)
    (area : 0 ≤ A) (sine : 0 < t)
    (small : d ≤ 1 → S * d ≤ 4 / (cos (d / 2) ^ 2 * t) * A)
    (large : S * d ≤ 8 / t * A) :
    S ≤ 4 / (s * cos (s / 2) ^ 2 * t) * A := by
  have s_le_one : s ≤ 1 := by linarith
  have d_positive := s_positive.trans_le separation
  have cs : 0 < cos (s / 2) := cos_div_two_pos s_positive.le s_le_one
  have denom_s : 0 < s * cos (s / 2) ^ 2 * t := by positivity
  by_cases d_small : d ≤ 1
  · have cd : 0 < cos (d / 2) := cos_div_two_pos d_positive.le d_small
    have ratio : s * cos (s / 2) ^ 2 * t ≤ d * cos (d / 2) ^ 2 * t :=
      mul_le_mul_of_nonneg_right
        (monotoneOn_diameter_mul_cos_sq ⟨s_positive.le, s_le_one⟩
          ⟨d_positive.le, d_small⟩ separation) sine.le
    calc
      S ≤ (4 / (cos (d / 2) ^ 2 * t) * A) / d := (le_div_iff₀ d_positive).2 (small d_small)
      _ = 4 / (d * cos (d / 2) ^ 2 * t) * A := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by norm_num) denom_s ratio) area
  · have denom_le : s * cos (s / 2) ^ 2 * t ≤ t / 2 := by
      have cos_sq : cos (s / 2) ^ 2 ≤ 1 := by
        simpa using pow_le_pow_left₀ cs.le (cos_le_one (s / 2)) 2
      have prod : s * cos (s / 2) ^ 2 ≤ 1 / 2 := by
        exact (mul_le_of_le_one_right s_positive.le cos_sq).trans s_small
      linarith [mul_le_mul_of_nonneg_right prod sine.le]
    calc
      S ≤ (8 / t * A) / d := (le_div_iff₀ d_positive).2 large
      _ ≤ 8 / t * A := div_le_self (by positivity) (le_of_not_ge d_small)
      _ = 4 / (t / 2) * A := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by norm_num) denom_s denom_le) area

/-- The two Crofton cases give the same area-proportional charge budget. The
crossing hypotheses use the endpoint portion bound in the small-diameter case
and total network length in the other case. -/
theorem expectedCharge_le_area {e l s ψ t d S A charge : ℝ}
    (edges : 0 ≤ e) (length : 0 ≤ l) (s_positive : 0 < s) (s_small : s ≤ 1 / 2)
    (incident : 0 < sin (ψ / 2)) (sine : 0 < t) (diameter : 0 ≤ d) (area : 0 ≤ A)
    (small_sides : d ≤ 1 → S * d ≤ 4 / (cos (d / 2) ^ 2 * t) * A)
    (large_sides : S * d ≤ 8 / t * A)
    (local_crossings : d < s → charge ≤ (e / sin (ψ / 2)) * (S * d) / (4 * π))
    (all_crossings : s ≤ d → charge ≤ l * S / (4 * π ^ 2)) :
    charge ≤ (componentCoefficient e l s ψ / t) * (A / (4 * π)) := by
  have s_le_one : s ≤ 1 := by linarith
  have cs := cos_div_two_pos s_positive.le s_le_one
  have positive : 0 < 4 * π := by positivity
  have weight {q : ℝ} (bound : q ≤ max (e / sin (ψ / 2)) (l / (π * s))) :
      q * (4 / (cos (s / 2) ^ 2 * t) * A) / (4 * π) ≤
        (componentCoefficient e l s ψ / t) * (A / (4 * π)) := by
    calc
      _ ≤ max (e / sin (ψ / 2)) (l / (π * s)) *
            (4 / (cos (s / 2) ^ 2 * t) * A) / (4 * π) :=
        (div_le_div_iff_of_pos_right positive).2 (mul_le_mul_of_nonneg_right bound (by positivity))
      _ = _ := by unfold componentCoefficient; ring
  by_cases d_small : d < s
  · have d_le_one := d_small.le.trans s_le_one
    have cd := cos_div_two_pos diameter d_le_one
    have cos_comp := cos_le_cos_of_nonneg_of_le_pi
      (show 0 ≤ d / 2 by positivity) (show s / 2 ≤ π by linarith [pi_gt_three])
      (show d / 2 ≤ s / 2 by linarith)
    have div_comp : 4 / (cos (d / 2) ^ 2 * t) ≤ 4 / (cos (s / 2) ^ 2 * t) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ cs.le cos_comp 2) sine.le)
    have shorter := (small_sides d_le_one).trans (mul_le_mul_of_nonneg_right div_comp area)
    apply (local_crossings d_small).trans
    apply ((div_le_div_iff_of_pos_right positive).2
      (mul_le_mul_of_nonneg_left shorter (div_nonneg edges incident.le))).trans
    exact weight (le_max_left _ _)
  · have separation := le_of_not_gt d_small
    have perimeter := residualPerimeter_le_of_separation s_positive s_small separation
      area sine small_sides large_sides
    calc
      charge ≤ l * S / (4 * π ^ 2) := all_crossings separation
      _ ≤ l * (4 / (s * cos (s / 2) ^ 2 * t) * A) / (4 * π ^ 2) :=
        (div_le_div_iff_of_pos_right (by positivity)).2 (mul_le_mul_of_nonneg_left perimeter length)
      _ = (l / (π * s)) * (4 / (cos (s / 2) ^ 2 * t) * A) / (4 * π) := by
        field_simp
      _ ≤ _ := weight (le_max_right _ _)

/-- The sphere's total area cancels the common charge weight in the rotation average. -/
theorem exists_net_partition_of_area_charge_bounds
    {Face Rotation Label Polygon : Type*} [Fintype Face] [Fintype Polygon]
    [MeasurableSpace Rotation] (C : TriangleComplex Face) (μ : Measure Rotation)
    [IsProbabilityMeasure μ] (bad : Set Rotation) (null : μ bad = 0)
    (label : Rotation → Face → Label) (charge : Polygon → Rotation → ℝ)
    (charge_integrable : ∀ p, Integrable (charge p) μ) (area : Polygon → ℝ)
    (total_area : (∑ p, area p) = 4 * π) (budget : ℝ)
    (expected : ∀ p, (∫ r, charge p r ∂μ) ≤ budget * (area p / (4 * π)))
    (counting : ∀ r ∉ bad,
      (Nat.card (C.labeledSeamGraph (label r)).ConnectedComponent : ℝ) = 2 + ∑ p, charge p r)
    (net : ∀ r ∉ bad, ∀ c : (C.labeledSeamGraph (label r)).ConnectedComponent,
      C.HasOriginalEdgeNet c.supp) :
    ∃ n : ℕ, (n : ℝ) ≤ 2 + budget ∧ C.HasNetPartition n := by
  exact exists_net_partition_of_expected_component_charges C μ bad null label charge
    charge_integrable (fun p => budget * (area p / (4 * π))) expected counting net
    |>.imp (fun n hn => ⟨by
      have sum_budget : (∑ p, budget * (area p / (4 * π))) = budget := by
        rw [← Finset.mul_sum, ← Finset.sum_div, total_area,
          div_self (by positivity : 4 * π ≠ 0), mul_one]
      simpa only [sum_budget] using hn.1, hn.2⟩)

end Unfoldings.FewestNets
