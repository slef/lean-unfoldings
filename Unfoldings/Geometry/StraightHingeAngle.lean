module

public import Unfoldings.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Tactic

/-! Turn through a crease transverse to a projected straight path. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real Set InnerProductGeometry

/-- Cosine of the angle from the crease direction `(a,b,c)` to the lifted
straight direction `(1,0,p)`. The projected path is aligned with the first axis. -/
def straightHingeCos (a b c p : ℝ) : ℝ :=
  (a + c * p) / (sqrt (a ^ 2 + b ^ 2 + c ^ 2) * sqrt (1 + p ^ 2))

/-- The unsigned intrinsic angle to the crease. -/
def straightHingeAngle (a b c p : ℝ) : ℝ := arccos (straightHingeCos a b c p)

/-- The second slope component in the plane containing the crease. -/
def straightHingeTransverse (a b c p : ℝ) : ℝ := (c - a * p) / b

private theorem straightHingeCos_hasDerivAt {a b c p : ℝ} (transverse : b ≠ 0) :
    HasDerivAt (straightHingeCos a b c)
      ((c - a * p) / (sqrt (a ^ 2 + b ^ 2 + c ^ 2) * sqrt (1 + p ^ 2) * (1 + p ^ 2))) p := by
  have rpos : 0 < a ^ 2 + b ^ 2 + c ^ 2 := by positivity
  have tpos : 0 < 1 + p ^ 2 := by positivity
  have r := sqrt_pos.2 rpos
  have t := sqrt_pos.2 tpos
  have tsq := sq_sqrt tpos.le
  have num : HasDerivAt (fun x => a + c * x) c p := by
    simpa using ((hasDerivAt_id p).const_mul c).const_add a
  have denomSq : HasDerivAt (fun x => 1 + x ^ 2) (2 * p) p := by
    simpa using ((hasDerivAt_id p).pow 2).const_add 1
  have denom := (denomSq.sqrt tpos.ne').const_mul (sqrt (a ^ 2 + b ^ 2 + c ^ 2))
  have core := num.div denom (mul_ne_zero r.ne' t.ne')
  unfold straightHingeCos
  convert core using 1
  field_simp [r.ne', t.ne', tpos.ne']
  ring_nf
  rw [tsq]
  ring

private theorem one_sub_straightHingeCos_sq {a b c p : ℝ} (transverse : b ≠ 0) :
    1 - straightHingeCos a b c p ^ 2 =
      (b ^ 2 * (1 + p ^ 2 + straightHingeTransverse a b c p ^ 2)) /
        ((a ^ 2 + b ^ 2 + c ^ 2) * (1 + p ^ 2)) := by
  have rpos : 0 < a ^ 2 + b ^ 2 + c ^ 2 := by positivity
  have tpos : 0 < 1 + p ^ 2 := by positivity
  rw [straightHingeCos, div_pow, mul_pow, sq_sqrt rpos.le, sq_sqrt tpos.le,
    straightHingeTransverse]
  field_simp [transverse]
  ring

/-- The arccosine of the two spatial directions is differentiable across
the entire range of directional slopes when the crease is transverse. -/
theorem straightHingeAngle_hasDerivAt {a b c p : ℝ} (transverse : b ≠ 0) :
    HasDerivAt (straightHingeAngle a b c)
      (-(1 / sqrt (1 - straightHingeCos a b c p ^ 2)) *
        ((c - a * p) / (sqrt (a ^ 2 + b ^ 2 + c ^ 2) * sqrt (1 + p ^ 2) * (1 + p ^ 2)))) p := by
  have complement : 0 < 1 - straightHingeCos a b c p ^ 2 := by
    rw [one_sub_straightHingeCos_sq transverse]
    positivity
  have neg : straightHingeCos a b c p ≠ -1 := by
    intro eq
    rw [eq] at complement
    norm_num at complement
  have pos : straightHingeCos a b c p ≠ 1 := by
    intro eq
    rw [eq] at complement
    norm_num at complement
  exact (hasDerivAt_arccos neg pos).comp p (straightHingeCos_hasDerivAt transverse)

private theorem sqrt_one_sub_straightHingeCos_sq {a b c p : ℝ} (transverse : b ≠ 0) :
    sqrt (1 - straightHingeCos a b c p ^ 2) =
      |b| * sqrt (1 + p ^ 2 + straightHingeTransverse a b c p ^ 2) /
        (sqrt (a ^ 2 + b ^ 2 + c ^ 2) * sqrt (1 + p ^ 2)) := by
  rw [one_sub_straightHingeCos_sq transverse, sqrt_div (by positivity), sqrt_mul (sq_nonneg b),
    sqrt_sq_eq_abs, sqrt_mul (by positivity)]

/-- At a transverse crease, the rate in directional-slope coordinates is
the transverse component of the unit normal times the arctangent rate. -/
theorem abs_deriv_straightHingeAngle {a b c p : ℝ} (transverse : b ≠ 0) :
    |deriv (straightHingeAngle a b c) p| =
      |straightHingeTransverse a b c p| /
        ((1 + p ^ 2) * sqrt (1 + p ^ 2 + straightHingeTransverse a b c p ^ 2)) := by
  have r : 0 < sqrt (a ^ 2 + b ^ 2 + c ^ 2) := by positivity
  have t : 0 < sqrt (1 + p ^ 2) := by positivity
  have q : 0 < sqrt (1 + p ^ 2 + straightHingeTransverse a b c p ^ 2) := by positivity
  have tabs : 0 < 1 + p ^ 2 := by positivity
  have babs := abs_pos.mpr transverse
  rw [(straightHingeAngle_hasDerivAt transverse).deriv, sqrt_one_sub_straightHingeCos_sq transverse]
  simp only [abs_mul, abs_neg, abs_div, abs_one, abs_abs, abs_of_pos r, abs_of_pos t,
    abs_of_pos q, abs_of_pos tabs]
  unfold straightHingeTransverse
  rw [abs_div]
  have q' : 0 < sqrt (1 + p ^ 2 + ((c - a * p) / b) ^ 2) := q
  field_simp [r.ne', t.ne', q'.ne', tabs.ne', babs.ne']

/-- A transverse crease contributes at most the change of the directional
arctangent times a uniform bound on the transverse component of the normal. -/
theorem abs_straightHingeAngle_sub_le {a b c p₀ p₁ S : ℝ} (transverse : b ≠ 0)
    (ordered : p₀ ≤ p₁)
    (bound : ∀ p ∈ Ioo p₀ p₁, |straightHingeTransverse a b c p| ≤
      S * sqrt (1 + p ^ 2 + straightHingeTransverse a b c p ^ 2)) :
    |straightHingeAngle a b c p₁ - straightHingeAngle a b c p₀| ≤
      S * (arctan p₁ - arctan p₀) := by
  rcases lt_or_eq_of_le ordered with lt | rfl
  · let f := straightHingeAngle a b c
    have differentiable : Differentiable ℝ f :=
      fun _ => (straightHingeAngle_hasDerivAt transverse).differentiableAt
    obtain ⟨p, hp, mean⟩ := exists_ratio_deriv_eq_ratio_slope f lt
      differentiable.continuous.continuousOn differentiable.differentiableOn arctan
      continuous_arctan.continuousOn
      (fun z _ => (hasDerivAt_arctan z).differentiableAt.differentiableWithinAt)
    have inc : 0 ≤ arctan p₁ - arctan p₀ := sub_nonneg.mpr (arctan_strictMono.monotone ordered)
    have speed : 0 < 1 / (1 + p ^ 2) := by positivity
    rw [(hasDerivAt_arctan p).deriv] at mean
    have abs_mean := congrArg abs mean
    rw [abs_mul, abs_of_nonneg inc, abs_mul, abs_of_pos speed] at abs_mean
    have ratio_pos : 0 < sqrt (1 + p ^ 2 + straightHingeTransverse a b c p ^ 2) := by
      positivity
    have rate : |deriv f p| ≤ S * (1 / (1 + p ^ 2)) := by
      change |deriv (straightHingeAngle a b c) p| ≤ _
      rw [abs_deriv_straightHingeAngle transverse, mul_comm (1 + p ^ 2), ← div_div]
      rw [mul_one_div, div_le_div_iff_of_pos_right (by positivity : 0 < 1 + p ^ 2)]
      exact (div_le_iff₀ ratio_pos).mpr (bound p hp)
    have weighted := mul_le_mul_of_nonneg_left rate inc
    rw [abs_mean] at weighted
    dsimp [f] at weighted
    apply (le_of_mul_le_mul_right ?_ speed)
    linarith only [weighted]
  · simp

end Unfoldings
