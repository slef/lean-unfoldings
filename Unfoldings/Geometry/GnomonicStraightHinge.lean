module

public import Unfoldings.Geometry.GnomonicTraceTransport
public import Unfoldings.Geometry.StraightHingeTurn

/-! The transported angle is the actual corner angle of a horizontal section. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real InnerProductGeometry

/-- The hinge in the planes with normals on a gnomonic line is transverse to the
horizontal closing link. Its ordinary spatial angle has the exact real lift. -/
theorem straightHingeAngle_eq_gnomonicAngle (m b p : ℝ) :
    straightHingeAngle (-m) 1 (-b) (-p) = π / 2 - arctan (gnomonicHingeRatio m b p) := by
  let q := m * p + b
  let d := √(1 + p ^ 2 + q ^ 2)
  let n := b * p - m
  let c := 1 + m ^ 2 + b ^ 2
  let C := √c
  let P := √(1 + p ^ 2)
  have dp : 0 < d := sqrt_pos.mpr (by positivity)
  have Cp : 0 < C := sqrt_pos.mpr (by dsimp [c]; positivity)
  have Pp : 0 < P := sqrt_pos.mpr (by positivity)
  have ds : d ^ 2 = 1 + p ^ 2 + q ^ 2 := sq_sqrt (by positivity)
  have Cs : C ^ 2 = c := sq_sqrt (by dsimp [c]; positivity)
  have Ps : P ^ 2 = 1 + p ^ 2 := sq_sqrt (by positivity)
  have total : d ^ 2 + n ^ 2 = c * (1 + p ^ 2) := by
    rw [ds]
    dsimp [n, q, c]
    ring
  have scalar : √(1 + (n / d) ^ 2) = C * P / d := by
    apply (sq_eq_sq₀ (sqrt_nonneg _) (by positivity)).mp
    rw [sq_sqrt (by positivity), div_pow, div_pow, mul_pow, Cs, Ps, ← total]
    field_simp [dp.ne']
  have cosine :
      straightHingeCos (-m) 1 (-b) (-p) = sin (arctan (gnomonicHingeRatio m b p)) := by
    rw [sin_arctan]
    change straightHingeCos (-m) 1 (-b) (-p) = (n / d) / √(1 + (n / d) ^ 2)
    rw [scalar]
    unfold straightHingeCos
    have base : √((-m) ^ 2 + (1 : ℝ) ^ 2 + (-b) ^ 2) = C := by dsimp [C, c]; congr 1; ring
    have height : √(1 + (-p) ^ 2) = P := by dsimp [P]; congr 1; ring
    rw [base, height]
    change (-m + (-b) * (-p)) / (C * P) = (n / d) / (C * P / d)
    field_simp [Cp.ne', Pp.ne', dp.ne']
    dsimp only [n]
    ring
  unfold straightHingeAngle
  rw [cosine, ← cos_pi_div_two_sub]
  exact arccos_cos (by linarith only [arctan_lt_pi_div_two (gnomonicHingeRatio m b p)])
    (by linarith only [neg_pi_div_two_lt_arctan (gnomonicHingeRatio m b p)])

/-- The hinge's earlier corner minus its later corner is exactly the real
transport change used by the signed normal-area computation. -/
theorem straightHinge_sub_eq_hingeAngleChange (m b p q : ℝ) :
    straightHingeAngle (-m) 1 (-b) (-p) - straightHingeAngle (-m) 1 (-b) (-q) =
      hingeAngleChange m b p q := by
  rw [straightHingeAngle_eq_gnomonicAngle, straightHingeAngle_eq_gnomonicAngle]
  unfold hingeAngleChange
  ring

end Unfoldings
