module

public import Unfoldings.Geometry.GnomonicAreaPrimitive

/-! Exact real transport across one straight segment of a normal trace. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real

/-- Along the normal line `q = m * p + b`, the ratio of the components
of the fixed hinge direction in the horizontal-axis frame. -/
def gnomonicHingeRatio (m b p : ℝ) : ℝ :=
  (b * p - m) / √(1 + p ^ 2 + (m * p + b) ^ 2)

/-- The hinge angle in the horizontal-axis frame changes by the integral of the
gnomonic connection form along a straight segment. -/
theorem hasDerivAt_gnomonicHingeAngle (m b p : ℝ) :
    HasDerivAt (fun x => arctan (gnomonicHingeRatio m b x))
      (gnomonicAreaPrimitive p (m * p + b)) p := by
  let q := m * p + b
  let d := √(1 + p ^ 2 + q ^ 2)
  let n := b * p - m
  let c := 1 + m ^ 2 + b ^ 2
  have square_pos : 0 < 1 + p ^ 2 + q ^ 2 := by positivity
  have dp : 0 < d := sqrt_pos.mpr square_pos
  have dsq : d ^ 2 = 1 + p ^ 2 + q ^ 2 := sq_sqrt square_pos.le
  have cp : 0 < c := by dsimp [c]; positivity
  have num : HasDerivAt (fun x : ℝ => b * x - m) b p := by
    convert (HasDerivAt.const_mul b (hasDerivAt_id p)).sub_const m using 1 <;>
      simp [id_eq]
  have base : HasDerivAt (fun x : ℝ => m * x + b) m p := by
    convert (HasDerivAt.const_mul m (hasDerivAt_id p)).add_const b using 1 <;>
      simp [id_eq]
  have base_square : HasDerivAt (fun x : ℝ => (m * x + b) ^ 2) (2 * q * m) p := by
    convert base.pow 2 using 1 <;> try rfl
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, q]
  have square : HasDerivAt (fun x : ℝ => 1 + x ^ 2 + (m * x + b) ^ 2)
      (2 * p + 2 * q * m) p := by
    refine HasDerivAt.add ?_ base_square
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using (hasDerivAt_pow 2 p).const_add 1
  have den : HasDerivAt (fun x : ℝ => √(1 + x ^ 2 + (m * x + b) ^ 2))
      ((2 * p + 2 * q * m) / (2 * d)) p :=
    square.sqrt square_pos.ne'
  have ratio_raw := HasDerivAt.fun_div num den dp.ne'
  have ratio : HasDerivAt (gnomonicHingeRatio m b) (q * c / d ^ 3) p := by
    convert ratio_raw using 1 <;> try rfl
    change q * c / d ^ 3 = (b * d - n * ((2 * p + 2 * q * m) / (2 * d))) / d ^ 2
    field_simp [dp.ne']
    linear_combination -b * dsq
  have angle := HasDerivAt.arctan ratio
  convert angle using 1 <;> try rfl
  change q / ((1 + p ^ 2) * d) = (1 / (1 + (n / d) ^ 2)) * (q * c / d ^ 3)
  have normalizer : d ^ 2 + n ^ 2 = (1 + p ^ 2) * c := by
    rw [dsq]
    dsimp [n, q, c]
    ring
  have quotient : 1 + (n / d) ^ 2 = ((1 + p ^ 2) * c) / d ^ 2 := by
    rw [div_pow, ← normalizer]
    field_simp [dp.ne']
  rw [quotient]
  field_simp [dp.ne', cp.ne', show (1 + p ^ 2) ≠ 0 by positivity]

/-- A real-valued primitive for transport along a nonvertical segment of the
normal trace. Vertical segments contribute zero in the same frame. -/
theorem integral_gnomonicHingeAngle (m b lo hi : ℝ) :
    (∫ p in lo..hi, gnomonicAreaPrimitive p (m * p + b)) =
      arctan (gnomonicHingeRatio m b hi) - arctan (gnomonicHingeRatio m b lo) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro p _
    exact hasDerivAt_gnomonicHingeAngle m b p
  · apply Continuous.intervalIntegrable
    unfold gnomonicAreaPrimitive
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro p
    positivity

end Unfoldings
