module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-! The real arctangent estimates for the coupled band-height calculation. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real MeasureTheory

/-- For positive scale, normalized arctangent is the integral of a scaled kernel. -/
theorem integral_scaled_arctan_kernel {a : ℝ} (positive : 0 < a) (y : ℝ) :
    (∫ t in (0 : ℝ)..y, (1 + (a * t) ^ 2)⁻¹) = arctan (a * y) / a := by
  let f (t : ℝ) := arctan (a * t) / a
  have integrable : IntervalIntegrable (fun t : ℝ => (1 + (a * t) ^ 2)⁻¹) volume 0 y := by
    apply Continuous.intervalIntegrable
    exact (show Continuous (fun t : ℝ => 1 + (a * t) ^ 2) by fun_prop).inv₀ (fun _ => by positivity)
  have deriv (t : ℝ) : HasDerivAt f ((1 + (a * t) ^ 2)⁻¹) t := by
    have mul_id : HasDerivAt (fun x : ℝ => a * x) a t := by
      simpa only [id_eq, mul_one] using HasDerivAt.const_mul a (hasDerivAt_id t)
    have raw := (HasDerivAt.arctan mul_id).div_const a
    convert raw using 1 <;> try rfl
    field_simp [positive.ne', show (1 + (a * t) ^ 2) ≠ 0 by positivity]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => deriv t) integrable]
  simp [f]

/-- The alternating fifth-order upper bound, on the entire nonnegative half-line. -/
theorem arctan_le_fifth {x : ℝ} (nonnegative : 0 ≤ x) :
    arctan x ≤ x - x ^ 3 / 3 + x ^ 5 / 5 := by
  let k (t : ℝ) := (1 + t ^ 2)⁻¹
  let p (t : ℝ) := 1 - t ^ 2 + t ^ 4
  have ck : Continuous k :=
    (show Continuous (fun t : ℝ => 1 + t ^ 2) by fun_prop).inv₀ (fun _ => by positivity)
  have cp : Continuous p := by fun_prop
  have integrate (t : ℝ) : HasDerivAt (fun s : ℝ => s - s ^ 3 / 3 + s ^ 5 / 5) (p t) t := by
    have h := ((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 3)).add
      ((hasDerivAt_pow 5 t).div_const 5)
    convert h using 1 <;> try rfl
    simp only [p, Nat.cast_ofNat, Nat.reduceSub]
    ring
  have upper := intervalIntegral.integral_mono_on (μ := volume) nonnegative
    (ck.intervalIntegrable 0 x) (cp.intervalIntegrable 0 x) (fun t ht => by
      change (1 + t ^ 2)⁻¹ ≤ 1 - t ^ 2 + t ^ 4
      rw [← one_div]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith only [show 0 ≤ t ^ 6 from pow_nonneg ht.1 _])
  have eq₀ : (∫ t in (0 : ℝ)..x, k t) = arctan x := by
    simpa [k] using (integral_inv_one_add_sq (a := 0) (b := x))
  have eq₁ : (∫ t in (0 : ℝ)..x, p t) = x - x ^ 3 / 3 + x ^ 5 / 5 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => integrate t)
      (cp.intervalIntegrable 0 x)]
    norm_num
  rwa [eq₀, eq₁] at upper

/-- The change in normalized arctangent costs at most the integral of the
leading quadratic error of its kernel. -/
theorem scaled_arctan_difference_le {a A y : ℝ} (ap : 0 < a) (order : a ≤ A)
    (nonnegative : 0 ≤ y) :
    arctan (a * y) / a - arctan (A * y) / A ≤ (A ^ 2 - a ^ 2) * y ^ 3 / 3 := by
  let k (c t : ℝ) := (1 + (c * t) ^ 2)⁻¹
  let p (t : ℝ) := (A ^ 2 - a ^ 2) * t ^ 2
  have ck (c : ℝ) : Continuous (k c) :=
    (show Continuous (fun t : ℝ => 1 + (c * t) ^ 2) by fun_prop).inv₀ (fun _ => by positivity)
  have cp : Continuous p := by fun_prop
  have comparison := intervalIntegral.integral_mono_on (μ := volume) nonnegative
    (((ck a).sub (ck A)).intervalIntegrable 0 y) (cp.intervalIntegrable 0 y) (fun t ht => by
      change k a t - k A t ≤ p t
      have xs := pow_le_pow_left₀ ap.le order 2
      have pn : 0 ≤ p t := mul_nonneg (sub_nonneg.mpr xs) (sq_nonneg _)
      have den : 1 ≤ (1 + (a * t) ^ 2) * (1 + (A * t) ^ 2) := by
        nlinarith only [sq_nonneg (a * t), sq_nonneg (A * t), sq_nonneg (a * A * t ^ 2)]
      have sa : 0 < 1 + (a * t) ^ 2 := by positivity
      have sb : 0 < 1 + (A * t) ^ 2 := by positivity
      have equal : k a t - k A t = p t / ((1 + (a * t) ^ 2) * (1 + (A * t) ^ 2)) := by
        unfold k p
        field_simp [sa.ne', sb.ne']
        ring
      rw [equal]
      exact (div_le_iff₀ (mul_pos sa sb)).mpr (le_mul_of_one_le_right pn den))
  change (∫ t in (0 : ℝ)..y, k a t - k A t) ≤ ∫ t in (0 : ℝ)..y, p t at comparison
  rw [intervalIntegral.integral_sub ((ck a).intervalIntegrable 0 y)
    ((ck A).intervalIntegrable 0 y), integral_scaled_arctan_kernel ap,
    integral_scaled_arctan_kernel (ap.trans_le order)] at comparison
  unfold p at comparison
  rw [intervalIntegral.integral_const_mul, integral_pow] at comparison
  norm_num at comparison
  have product : (A ^ 2 - a ^ 2) * (y ^ 3 / 3) = (A ^ 2 - a ^ 2) * y ^ 3 / 3 := by ring
  rw [product] at comparison
  linarith only [comparison]

/-- For any positive numerator the arctangent of a reciprocal is convex as a
function of its positive denominator. -/
theorem convexOn_arctan_div {c : ℝ} (cp : 0 < c) :
    ConvexOn ℝ (Set.Ioi 0) (fun t : ℝ => arctan (c / t)) := by
  let f (t : ℝ) := arctan (c / t)
  have derivatives {t : ℝ} (tp : 0 < t) :
      HasDerivAt f (-(c / (t ^ 2 + c ^ 2))) t := by
    have ratio : HasDerivAt (fun x : ℝ => c / x) (-(c / t ^ 2)) t := by
      have h := HasDerivAt.fun_div (hasDerivAt_const t c) (hasDerivAt_id t) tp.ne'
      convert h using 1 <;> simp [id_eq]
      ring
    have angle := HasDerivAt.arctan ratio
    convert angle using 1 <;> try rfl
    change -(c / (t ^ 2 + c ^ 2)) = 1 / (1 + (c / t) ^ 2) * -(c / t ^ 2)
    field_simp [tp.ne']
  apply MonotoneOn.convexOn_of_deriv (convex_Ioi 0)
  · exact continuous_arctan.comp_continuousOn
      (continuousOn_const.div continuousOn_id (fun _ h => (Set.mem_Ioi.mp h).ne'))
  · intro t ht
    exact (derivatives (Set.mem_Ioi.mp (interior_subset ht))).differentiableAt.differentiableWithinAt
  · intro s hs t ht order
    have sp := Set.mem_Ioi.mp (interior_subset hs)
    have tp := Set.mem_Ioi.mp (interior_subset ht)
    rw [(derivatives sp).deriv, (derivatives tp).deriv, neg_le_neg_iff]
    apply div_le_div_of_nonneg_left cp.le (by positivity)
    exact add_le_add_left (pow_le_pow_left₀ sp.le order 2) _

theorem convexOn_inv_pos : ConvexOn ℝ (Set.Ioi 0) (fun t : ℝ => t⁻¹) := by
  have derivatives {t : ℝ} (tp : 0 < t) : HasDerivAt (fun x : ℝ => x⁻¹) (-(1 / t ^ 2)) t := by
    convert HasDerivAt.inv (hasDerivAt_id t) tp.ne' using 1
    all_goals first | rfl | (simp [id_eq, neg_div, one_div, inv_pow] <;> ring)
  apply MonotoneOn.convexOn_of_deriv (convex_Ioi 0)
  · exact continuousOn_id.inv₀ (fun _ h => (Set.mem_Ioi.mp h).ne')
  · intro t ht
    exact (derivatives (Set.mem_Ioi.mp (interior_subset ht))).differentiableAt.differentiableWithinAt
  · intro s hs t ht order
    have sp := Set.mem_Ioi.mp (interior_subset hs)
    have tp := Set.mem_Ioi.mp (interior_subset ht)
    rw [(derivatives sp).deriv, (derivatives tp).deriv, neg_le_neg_iff]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact pow_le_pow_left₀ sp.le order 2

end Unfoldings
