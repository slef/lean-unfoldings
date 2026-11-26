module

public import Unfoldings.FewestNets.RevisedLatitudeSelectorBoundary
public import Unfoldings.FewestNets.SphericalSelectorMetric
public import Unfoldings.FewestNets.RevisedLatitudeAnnularCorners

/-! Verify the literal sides and corners meet the revised per-selector counting budgets. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real Cap InnerProductGeometry SphericalSelectorBoundary

private theorem sum_endpointFactors_of_permutation {J : Type*} [Fintype J]
    (L : ℝ) (corner : J → ℝ) (step : Equiv.Perm J) :
    (∑ p : J × Bool, L / (sin L * sin (min (corner (if p.2 then step p.1 else p.1)) (π / 2)))) / π =
      ∑ j : J, (2 * L / (π * sin L)) / sin (min (corner j) (π / 2)) := by
  let factor (j : J) := L / (sin L * sin (min (corner j) (π / 2)))
  change (∑ p : J × Bool, factor (if p.2 then step p.1 else p.1)) / π = _
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
  rw [Finset.sum_add_distrib, Equiv.sum_comp step factor, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp only [factor, div_eq_mul_inv, mul_inv]
  ring

/-- Every spherical annular corner has positive angle. -/
theorem annular_corner_pos {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (i : AnnularTriangle a) (j : Fin 3) : 0 < annularCornerAngle i j := by
  have sine := annular_spherical_capped_sines positive small i
  have strict : 0 < sin (min (annularCornerAngle i j) (π / 2)) := by
    by_cases apex : j = 2
    · subst j
      by_contra! hin
      have cp : 0 ≤ (annularApexCoefficient i - 0.073 * a) * (rowStep a / spacing a) :=
        mul_nonneg (apexCountCoefficient_pos small _ _).le
          (div_nonneg (rowStep_pos positive small).le (spacing_pos positive).le)
      exact (not_le_of_gt zero_lt_one) (sine.1.trans (mul_nonpos_of_nonneg_of_nonpos cp hin))
    · exact (by norm_num : (0 : ℝ) < 0.932).trans (sine.2 _ apex)
  by_contra! upper
  have zero : annularCornerAngle i j = 0 := upper.antisymm (angle_nonneg _ _)
  rw [zero, min_eq_left pi_div_two_pos.le, sin_zero] at strict
  exact (lt_irrefl _) strict

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

set_option maxHeartbeats 1500000 in
/-- All pairs of annular sides are incident, so 0.11 is a valid separation
scale. Each endpoint uses its actual spherical angle. -/
def annularSelectorMetric (i : AnnularTriangle a) :
    MetricData (annularSelectorBoundary positive small i) where
  longest := annularLongestSide i
  longest_pos := (annularSideLength_pos positive small i 0).trans_le (le_max_left _ _)
  longest_small := by
    have bound := (annular_metric_bounds positive small i).1
    exact max_le (by linarith only [pi_gt_d2, bound 0])
      (max_le (by linarith only [pi_gt_d2, bound 1]) (by linarith only [pi_gt_d2, bound 2]))
  side_pos := annularSideLength_pos positive small i
  side_le := fun j => by
    change annularSideLength i j ≤ annularLongestSide i
    fin_cases j
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  separation := 0.11
  separation_pos := by norm_num
  separation_small := by norm_num
  separated := by
    intro j k different nonincident x hx y hy
    have endpoints : ∃ b c : Bool, (if b then j + 1 else j) = (if c then k + 1 else k) := by
      fin_cases j <;> fin_cases k <;> first | exact False.elim (different rfl) | decide
    obtain ⟨b, c, eq⟩ := endpoints
    exact (nonincident b c (congrArg ((rings a).annularVertices i) eq)).elim
  corner := fun j b => annularCornerAngle i (if b then j + 1 else j)
  corner_pos := fun j b => annular_corner_pos positive small i _
  incident := by
    intro j k b c different common
    change (rings a).annularVertices i (if b then j + 1 else j) =
      (rings a).annularVertices i (if c then k + 1 else k) at common
    have same := annularVertex_injective positive small i common
    change annularCornerAngle i (if b then j + 1 else j) ≤
      angle (minorArcTangent (annularSideEndpoint i j b) (annularSideEndpoint i j (!b)))
        (minorArcTangent (annularSideEndpoint i k c) (annularSideEndpoint i k (!c)))
    fin_cases j <;> fin_cases k <;> cases b <;> cases c <;>
      first
      | exact False.elim (different rfl)
      | exact False.elim ((by decide : _ ≠ _) same)
      | exact le_rfl
      | exact (angle_comm _ _).le

/-- The geometric crossing budget of the actual annular selector. -/
theorem annularSelectorMetric_crossingBudget_le (i : AnnularTriangle a) :
    (annularSelectorMetric positive small i).crossingBudget ≤
      0.675 * ((annularApexCoefficient i - 0.073 * a) * (rowStep a / spacing a) + 2 / 0.932) := by
  let M := annularSelectorMetric positive small i
  let L := annularLongestSide i
  let c := 2 * L / (π * sin L)
  let A := (annularApexCoefficient i - 0.073 * a) * (rowStep a / spacing a)
  have sum := sum_endpointFactors_of_permutation L (annularCornerAngle i) (finRotate 3)
  simp only [finRotate_apply] at sum
  change max
    ((∑ p : Fin 3 × Bool, L / (sin L *
      sin (min (annularCornerAngle i (if p.2 then p.1 + 1 else p.1)) (π / 2)))) / π)
    (annularPerimeter i / (π * 0.11)) ≤ 0.675 * (A + 2 / 0.932)
  rw [sum]
  obtain ⟨cp, cb⟩ := annular_longestSide_factor positive small i
  obtain ⟨apex, base⟩ := annular_spherical_capped_sines positive small i
  apply max_le
  · let s j := sin (min (annularCornerAngle i j) (π / 2))
    have Apos : 0 < A :=
      mul_pos (apexCountCoefficient_pos small _ _) (div_pos (rowStep_pos positive small) (spacing_pos positive))
    have apex_pos : 0 < s 2 := by
      by_contra! nn
      exact (not_le_of_gt zero_lt_one) (apex.trans (mul_nonpos_of_nonneg_of_nonpos Apos.le nn))
    have ha : c / s 2 ≤ 0.675 * A := by
      have hi : 1 / s 2 ≤ A := (div_le_iff₀ apex_pos).mpr apex
      calc
        _ ≤ 0.675 / s 2 := div_le_div_of_nonneg_right cb apex_pos.le
        _ = 0.675 * (1 / s 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hi (by norm_num)
    have hb (j : Fin 3) (hj : j ≠ 2) : c / s j ≤ 0.675 / 0.932 := by
      have h : 0.932 < s j := base j hj
      exact (div_le_div_of_nonneg_right cb (by linarith only [h])).trans
        (div_le_div_of_nonneg_left (by norm_num) (by norm_num) h.le)
    change (∑ j, c / s j) ≤ _
    rw [Fin.sum_univ_three]
    have h := add_le_add (add_le_add (hb 0 (by decide)) (hb 1 (by decide))) ha
    ring_nf at h ⊢
    exact h
  · have perimeter : annularPerimeter i / (π * 0.11) ≤ 3.84 := by
      apply (div_le_iff₀ (mul_pos pi_pos (by norm_num))).mpr
      linarith only [(annular_metric_bounds positive small i).2, radius_lt small, pi_gt_d4]
    have coff : 1.186 ≤ annularApexCoefficient i - 0.073 * a := by
      unfold annularApexCoefficient apexCountCoefficient
      split_ifs <;> linarith only [small, pi_lt_d6]
    have step : 0.852 / 0.268 ≤ rowStep a / spacing a := by
      apply (le_div_iff₀ (spacing_pos positive)).mpr
      have b := spacing_lt positive small
      have d := (rowStep_bounds positive small).1
      ring_nf
      linarith only [b, d]
    apply perimeter.trans
    have lower := mul_le_mul coff step (by norm_num) (by linarith only [coff])
    dsimp only [A]
    ring_nf at lower ⊢
    linarith only [lower]

end Unfoldings.FewestNets.RevisedLatitudeGrid
