module

public import Unfoldings.Geometry.Angles
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic.GCongr

/-! Exact substitution in the two endpoint component-count estimates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real
open scoped BigOperators

/-- Chord length of a unit regular icosahedron edge. -/
def icosahedronEdge : ℝ := 4 / √(10 + 2 * √5)

/-- The coefficient of the reciprocal corner-angle sine in the paper's count. -/
def componentCoefficient (edges length separation incidentAngle : ℝ) : ℝ :=
  4 / cos (separation / 2) ^ 2 *
    max (edges / sin (incidentAngle / 2)) (length / (π * separation))

/-- An upper bound on all three corners gives the lower bound used for counting. -/
theorem cornerAngle_lower_of_upper (T : Triangle) (θ : ℝ)
    (bound : ∀ i, T.cornerAngle i ≤ θ) (i : Fin 3) :
    π - 2 * θ ≤ T.cornerAngle i := by
  have total := T.sum_cornerAngle
  rw [Fin.sum_univ_three] at total
  fin_cases i
  · change π - 2 * θ ≤ T.cornerAngle 0
    linarith [bound 1, bound 2]
  · change π - 2 * θ ≤ T.cornerAngle 1
    linarith [bound 0, bound 2]
  · change π - 2 * θ ≤ T.cornerAngle 2
    linarith [bound 0, bound 1]

private theorem sqrt_five_bounds : 2.23606 < √(5 : ℝ) ∧ √(5 : ℝ) < 2.23607 := by
  constructor
  · exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  · exact (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)

private theorem edge_bounds : 1.05146 < icosahedronEdge ∧ icosahedronEdge < 1.052 := by
  have d_pos : 0 < 10 + 2 * √(5 : ℝ) := by positivity
  have hi : √(10 + 2 * √(5 : ℝ)) < 3.804231 := by
    apply (Real.sqrt_lt d_pos.le (by norm_num)).2
    linarith [sqrt_five_bounds.2]
  have lo : 3.804 < √(10 + 2 * √(5 : ℝ)) := by
    apply (Real.lt_sqrt (by norm_num)).2
    linarith [sqrt_five_bounds.1]
  unfold icosahedronEdge
  have denom_pos := Real.sqrt_pos.2 d_pos
  constructor
  · apply (lt_div_iff₀ denom_pos).2
    have h := mul_lt_mul_of_pos_left hi (show (0 : ℝ) < 1.05146 by norm_num)
    linarith
  · apply (div_lt_iff₀ denom_pos).2
    have h := mul_lt_mul_of_pos_left lo (show (0 : ℝ) < 1.052 by norm_num)
    linarith

private theorem cos_sq_small_separation {s : ℝ} (nonneg : 0 ≤ s) (small : s < 0.002) :
    (0.999999 : ℝ) < cos (s / 2) ^ 2 := by
  have sq := pow_lt_pow_left₀ (show s / 2 < 0.001 by linarith)
    (show 0 ≤ s / 2 by positivity) (show (2 : ℕ) ≠ 0 by decide)
  have lower : 0.9999995 < cos (s / 2) := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := s / 2)]
  have sq_lower := pow_lt_pow_left₀ lower (show (0 : ℝ) ≤ 0.9999995 by norm_num)
    (show (2 : ℕ) ≠ 0 by decide)
  linarith

private theorem sine_incident_100 : (0.7 : ℝ) < sin (107 * π / 360) := by
  have root : 1.4 < √(2 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  calc
    _ < sin (π / 4) := by rw [Real.sin_pi_div_four]; linarith
    _ < _ := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

private theorem sine_incident_400 : (0.809015 : ℝ) < sin (108 * π / 360) := by
  rw [show 108 * π / 360 = π / 2 - π / 5 by ring,
    Real.sin_pi_div_two_sub, Real.cos_pi_div_five]
  linarith [sqrt_five_bounds.1]

private theorem componentCoefficient_le_of_denominators {e l s ψ c a d : ℝ}
    (edges : 0 ≤ e) (length : 0 ≤ l) (hc : 0 < c) (ha : 0 < a) (hd : 0 < d)
    (cos_lower : c ≤ cos (s / 2) ^ 2) (sin_lower : a ≤ sin (ψ / 2))
    (separation_lower : d ≤ π * s) :
    componentCoefficient e l s ψ ≤ 4 / c * max (e / a) (l / d) := by
  have max_nonneg : 0 ≤ max (e / sin (ψ / 2)) (l / (π * s)) :=
    (div_nonneg edges (ha.le.trans sin_lower)).trans (le_max_left _ _)
  unfold componentCoefficient
  apply mul_le_mul _ _ max_nonneg (by positivity)
  · exact div_le_div_of_nonneg_left (by norm_num) hc cos_lower
  · exact max_le_max (div_le_div_of_nonneg_left edges ha sin_lower)
      (div_le_div_of_nonneg_left length hd separation_lower)

/-- The frequency-100 network bounds give the coefficient used in the first branch. -/
theorem componentCoefficient_q100 :
    componentCoefficient 300000 2084 (icosahedronEdge / 700) (107 * π / 180) <
      1767000 := by
  have s_pos : 0 ≤ icosahedronEdge / 700 := by linarith [edge_bounds.1]
  have s_small : icosahedronEdge / 700 < 0.002 := by linarith [edge_bounds.2]
  have cos_bound := (cos_sq_small_separation s_pos s_small).le
  have sin_bound : (0.7 : ℝ) ≤ sin ((107 * π / 180) / 2) := by
    rw [show (107 * π / 180) / 2 = 107 * π / 360 by ring]
    exact sine_incident_100.le
  have sep : (3.141592 * 1.05146 / 700 : ℝ) ≤ π * (icosahedronEdge / 700) := by
    have hp := mul_le_mul Real.pi_gt_d6.le edge_bounds.1.le (by norm_num) Real.pi_pos.le
    linarith only [hp]
  apply (componentCoefficient_le_of_denominators (e := 300000) (l := 2084) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) cos_bound sin_bound sep).trans_lt
  norm_num [max_def]

/-- The frequency-400 network bounds give the coefficient used in the second branch. -/
theorem componentCoefficient_q400 :
    componentCoefficient 4800000 8336 (icosahedronEdge / 2200) (108 * π / 180) <
      23733000 := by
  have s_pos : 0 ≤ icosahedronEdge / 2200 := by linarith [edge_bounds.1]
  have s_small : icosahedronEdge / 2200 < 0.002 := by linarith [edge_bounds.2]
  have cos_bound := (cos_sq_small_separation s_pos s_small).le
  have sin_bound : (0.809015 : ℝ) ≤ sin ((108 * π / 180) / 2) := by
    rw [show (108 * π / 180) / 2 = 108 * π / 360 by ring]
    exact sine_incident_400.le
  have sep : (3.141592 * 1.05146 / 2200 : ℝ) ≤ π * (icosahedronEdge / 2200) := by
    have hp := mul_le_mul Real.pi_gt_d6.le edge_bounds.1.le (by norm_num) Real.pi_pos.le
    linarith only [hp]
  apply (componentCoefficient_le_of_denominators (e := 4800000) (l := 8336) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) cos_bound sin_bound sep).trans_lt
  norm_num [max_def]

private theorem sine_pi_multiple_lower (t : ℝ) (positive : 0 < t) :
    3.141592 * t - (3.141593 * t) ^ 3 / 6 < sin (π * t) := by
  have lo := mul_lt_mul_of_pos_right Real.pi_gt_d6 positive
  have hi := mul_lt_mul_of_pos_right Real.pi_lt_d6 positive
  have pow_hi := pow_lt_pow_left₀ hi (mul_pos Real.pi_pos positive).le
    (show (3 : ℕ) ≠ 0 by decide)
  linarith [Real.sin_gt_sub_cube (mul_pos Real.pi_pos positive)]

/-- Exact final arithmetic at the first headline angle. -/
theorem endpoint_count_q100 :
    2 + 1767000 / cos (81 * π / 180) < (11300000 : ℝ) := by
  rw [← Real.sin_pi_div_two_sub, show π / 2 - 81 * π / 180 = π * (9 / 180) by ring]
  have lower := sine_pi_multiple_lower (9 / 180) (by norm_num)
  have upper := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1767000 by norm_num)
    (by norm_num : 0 < 3.141592 * (9 / 180 : ℝ) - (3.141593 * (9 / 180)) ^ 3 / 6)
    lower.le
  linarith

/-- Exact final arithmetic at the second headline angle. -/
theorem endpoint_count_q400 :
    2 + 23733000 / cos (83.2067 * π / 180) < (200700000 : ℝ) := by
  rw [← Real.sin_pi_div_two_sub,
    show π / 2 - 83.2067 * π / 180 = π * (6.7933 / 180) by ring]
  have lower := sine_pi_multiple_lower (6.7933 / 180) (by norm_num)
  have upper := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 23733000 by norm_num)
    (by norm_num : 0 < 3.141592 * (6.7933 / 180 : ℝ) - (3.141593 * (6.7933 / 180)) ^ 3 / 6)
    lower.le
  linarith

end Unfoldings.FewestNets
