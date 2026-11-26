module

public import Unfoldings.Cap.Gnomonic
public import Unfoldings.Geometry.GnomonicHingeTransport

/-! A tangent frame on the upper hemisphere adapted to horizontal normal coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open Real

private def coordinates (x y z : ℝ) : Space := WithLp.toLp 2 ![x, y, z]

private theorem coordinates_inner (x y z u v w : ℝ) :
    inner ℝ (coordinates x y z) (coordinates u v w) = x * u + y * v + z * w := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, Real.inner_apply, coordinates]
  rfl

/-- A unit tangent along increasing horizontal slope, independent of vertical slope. -/
def horizontalNormalFrame (p : ℝ) : Space :=
  (√(1 + p ^ 2))⁻¹ • WithLp.toLp 2 ![1, 0, -p]

/-- The second unit tangent, oriented toward increasing vertical slope. -/
def verticalNormalFrame (p q : ℝ) : Space :=
  (√(1 + p ^ 2) * √(1 + p ^ 2 + q ^ 2))⁻¹ • WithLp.toLp 2 ![-p * q, 1 + p ^ 2, -q]

/-- The consistently oriented hinge vector for a nonvertical straight normal line. -/
def normalLineHinge (m b : ℝ) : Space := WithLp.toLp 2 ![-m, 1, -b]

/-- The two frame vectors are tangent and orthonormal. -/
theorem gnomonicNormalFrame_orthonormal (p q : ℝ) :
    let h := horizontalNormalFrame p
    let v := verticalNormalFrame p q
    let n := northLift (WithLp.toLp 2 ![p, q])
    inner ℝ h n = 0 ∧ inner ℝ v n = 0 ∧ inner ℝ h v = 0 ∧
      inner ℝ h h = 1 ∧ inner ℝ v v = 1 := by
  let c := √(1 + p ^ 2)
  let d := √(1 + p ^ 2 + q ^ 2)
  have cp : 0 < c := sqrt_pos.mpr (by positivity)
  have dp : 0 < d := sqrt_pos.mpr (by positivity)
  have cs : c ^ 2 = 1 + p ^ 2 := sq_sqrt (by positivity)
  have ds : d ^ 2 = 1 + p ^ 2 + q ^ 2 := sq_sqrt (by positivity)
  change inner ℝ (c⁻¹ • coordinates 1 0 (-p)) (coordinates p q 1) = 0 ∧
    inner ℝ ((c * d)⁻¹ • coordinates (-p * q) (1 + p ^ 2) (-q)) (coordinates p q 1) = 0 ∧
    inner ℝ (c⁻¹ • coordinates 1 0 (-p)) ((c * d)⁻¹ • coordinates (-p * q) (1 + p ^ 2) (-q)) = 0 ∧
    inner ℝ (c⁻¹ • coordinates 1 0 (-p)) (c⁻¹ • coordinates 1 0 (-p)) = 1 ∧
    inner ℝ ((c * d)⁻¹ • coordinates (-p * q) (1 + p ^ 2) (-q))
      ((c * d)⁻¹ • coordinates (-p * q) (1 + p ^ 2) (-q)) = 1
  simp only [real_inner_smul_left, real_inner_smul_right, coordinates_inner]
  refine ⟨by ring, by ring, by ring, ?_, ?_⟩
  · have raw : 1 * 1 + 0 * 0 + -p * -p = c ^ 2 := by rw [cs]; ring
    rw [raw]
    field_simp [cp.ne']
  · have raw : (-p * q) * (-p * q) + (1 + p ^ 2) * (1 + p ^ 2) + -q * -q =
        (c * d) ^ 2 := by rw [mul_pow, cs, ds]; ring
    rw [raw]
    field_simp [cp.ne', dp.ne']

/-- The fixed hinge stays tangent along its entire normal segment. Its second
frame coordinate is positive, so the angle has a single real arctangent lift. -/
theorem normalLineHinge_frame (m b p : ℝ) :
    let q := m * p + b
    let h := horizontalNormalFrame p
    let v := verticalNormalFrame p q
    let e := normalLineHinge m b
    inner ℝ e (northLift (WithLp.toLp 2 ![p, q])) = 0 ∧
      0 < inner ℝ e v ∧
      inner ℝ e h / inner ℝ e v = gnomonicHingeRatio m b p := by
  let q := m * p + b
  let c := √(1 + p ^ 2)
  let d := √(1 + p ^ 2 + q ^ 2)
  have cp : 0 < c := sqrt_pos.mpr (by positivity)
  have dp : 0 < d := sqrt_pos.mpr (by positivity)
  have ds : d ^ 2 = 1 + p ^ 2 + q ^ 2 := sq_sqrt (by positivity)
  change inner ℝ (coordinates (-m) 1 (-b)) (coordinates p q 1) = 0 ∧
    0 < inner ℝ (coordinates (-m) 1 (-b)) ((c * d)⁻¹ • coordinates (-p * q) (1 + p ^ 2) (-q)) ∧
    inner ℝ (coordinates (-m) 1 (-b)) (c⁻¹ • coordinates 1 0 (-p)) /
      inner ℝ (coordinates (-m) 1 (-b)) ((c * d)⁻¹ • coordinates (-p * q) (1 + p ^ 2) (-q)) = _
  simp only [real_inner_smul_right, coordinates_inner]
  have transverse : (-m) * (-p * q) + 1 * (1 + p ^ 2) + (-b) * (-q) = d ^ 2 := by
    rw [ds]
    dsimp only [q]
    ring
  have vertical : (c * d)⁻¹ * (d ^ 2) = d / c := by field_simp [cp.ne', dp.ne']
  rw [transverse, vertical]
  refine ⟨by dsimp only [q]; ring, div_pos dp cp, ?_⟩
  change (c⁻¹ * ((-m) * 1 + 1 * 0 + (-b) * (-p))) / (d / c) = (b * p - m) / d
  field_simp [cp.ne', dp.ne']
  ring

/-- The frame along a vertical normal line shares one fixed tangent. -/
theorem vertical_normalLine_common_tangent (p q : ℝ) :
    inner ℝ (horizontalNormalFrame p) (northLift (WithLp.toLp 2 ![p, q])) = 0 :=
  (gnomonicNormalFrame_orthonormal p q).1

end Unfoldings.Cap
