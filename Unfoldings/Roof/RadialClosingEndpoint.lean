module

public import Unfoldings.Cap.SignedHeadingProjection
public import Unfoldings.Geometry.GnomonicRadialFrame
public import Unfoldings.Roof.SignedClosingHinge
public import Unfoldings.Roof.Gnomonic

/-! Exact endpoint transport in the pole-aligned chart of a closing section. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Cap InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

local notation "east" => (WithLp.toLp 2 ![(1 : ℝ), 0] : Plane)

/-- One section direction's error relative to its planar heading. -/
def sectionHeadingError (f : Face) (d : Plane) : ℝ :=
  projectionHeadingError (K.normal f) (K.sectionDirection f d)

theorem sectionHeadingError_east (f : Face) :
    K.sectionHeadingError f east = radialSectionHeading (K.normalSlope f 0) (K.normalSlope f 1) := by
  let p := K.normalSlope f 0
  let q := K.normalSlope f 1
  let d := √(1 + p ^ 2 + q ^ 2)
  have slope : (WithLp.toLp 2 ![p, q] : Plane) = K.normalSlope f := by ext i; fin_cases i <;> rfl
  have x : K.sectionDirection f east = WithLp.toLp 2 ![1, 0, -p] := K.sectionDirection_east f
  have east_complex : orientedComplex east = 1 := by apply Complex.ext <;> simp [Complex.one_re, Complex.one_im]
  unfold sectionHeadingError projectionHeadingError signedPlanarAngle
  rw [K.horizontal_sectionDirection, east_complex, div_one, ← K.gnomonicNormal_normalSlope, ← slope, x,
    alignedHorizontal_section_coordinates]
  let z := orientedComplex (WithLp.toLp 2 ![1 + p ^ 2 / (d + 1), p * q / (d + 1)])
  change z.arg = radialSectionHeading p q
  have zre : z.re = 1 + p ^ 2 / (d + 1) := by rw [show z = _ from rfl, orientedComplex_re]; rfl
  have zim : z.im = p * q / (d + 1) := by rw [show z = _ from rfl, orientedComplex_im]; rfl
  have re_pos : 0 < z.re := by rw [zre]; positivity
  obtain ⟨low, high⟩ := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl re_pos))
  rw [← Real.arctan_tan low high, Complex.tan_arg, zre, zim]
  unfold radialSectionHeading
  congr 1
  have h : 0 < d + 1 := by positivity
  have h' : 0 < d + 1 + p ^ 2 := by positivity
  field_simp [h.ne', h'.ne', (show 1 + p ^ 2 / (d + 1) ≠ 0 from zre ▸ re_pos.ne')]
  <;> ring

theorem abs_sectionHeadingError_le (f : Face) {c : ℝ} (pos : 0 < c) (tilt : c ≤ K.normal f 2)
    {x : Plane} (ne : x ≠ 0) : |K.sectionHeadingError f x| ≤ arcsin ((1 - c) / (1 + c)) :=
  abs_projectionHeadingError_le (K.normal_unit f) pos tilt (K.sectionDirection_ne_zero f ne)
    (K.sectionDirection_tangent f x)

theorem sectionHeadingError_eq_of_slope_eq {f g : Face} (same : K.normalSlope f = K.normalSlope g)
    (d : Plane) : K.sectionHeadingError f d = K.sectionHeadingError g d := by
  have h : K.normal f = K.normal g := by
    rw [← K.gnomonicNormal_normalSlope, ← K.gnomonicNormal_normalSlope, same]
  unfold sectionHeadingError
  rw [h, sectionDirection, sectionDirection, same]

@[simp] theorem sectionHeadingError_neg (f : Face) (d : Plane) :
    K.sectionHeadingError f (-d) = K.sectionHeadingError f d := by
  rw [sectionHeadingError, K.sectionDirection_neg, projectionHeadingError_neg]
  rfl

theorem sectionHeadingError_smul_of_pos (f : Face) {t : ℝ} (tp : 0 < t) (d : Plane) :
    K.sectionHeadingError f (t • d) = K.sectionHeadingError f d := by
  let n := K.normal f
  let v := K.sectionDirection f d
  have scaled : alignedHorizontal n (t • v) = t • alignedHorizontal n v := by
    unfold alignedHorizontal
    rw [map_smul, smul_sub, smul_smul]
    have coord : (t • v) 2 = t * v 2 := rfl
    rw [coord, mul_div_assoc]
  unfold sectionHeadingError projectionHeadingError
  rw [K.sectionDirection_smul]
  change signedPlanarAngle (horizontal (t • v)) (alignedHorizontal n (t • v)) =
    signedPlanarAngle (horizontal v) (alignedHorizontal n v)
  rw [map_smul, scaled, signedPlanarAngle_smul_of_pos tp tp]

/-- Giving the corner error the sign of its planar determinant recovers the
difference of the pole-aligned errors of its endpoint directions. -/
theorem signed_sectionAngle_sub_eq (f : Face) {x y : Plane} (nx : x ≠ 0) (ny : y ≠ 0) :
    (if 0 ≤ orient 0 x y then 1 else -1) *
      (angle (K.sectionDirection f x) (K.sectionDirection f y) - angle x y) =
        K.sectionHeadingError f y - K.sectionHeadingError f x := by
  let X := K.sectionDirection f x
  let Y := K.sectionDirection f y
  let n := K.normal f
  have nX := K.sectionDirection_ne_zero f nx
  have nY := K.sectionDirection_ne_zero f ny
  have tX := K.sectionDirection_tangent f x
  have tY := K.sectionDirection_tangent f y
  have unit := K.normal_unit f
  have up := K.normal_upward f
  have h := signed_projection_angle_sub_eq unit up nX nY tX tY
  let S := signedPlanarAngle (alignedHorizontal n X) (alignedHorizontal n Y)
  let P := signedPlanarAngle x y
  have sgnP : 0 ≤ P ↔ 0 ≤ orient 0 x y := by
    simpa only [P, orient, PiLp.zero_apply, sub_zero] using signedPlanarAngle_nonneg_iff x y nx
  have sgn : 0 ≤ S ↔ 0 ≤ orient 0 x y := by
    rw [show S = signedPlanarAngle (alignedHorizontal n X) (alignedHorizontal n Y) from rfl]
    rw [signedPlanarAngle_aligned_nonneg_iff unit up nX tX tY]
    rw [K.horizontal_sectionDirection, K.horizontal_sectionDirection]
    exact sgnP
  have absP : |P| = angle x y := abs_signedPlanarAngle _ _ nx ny
  have absS : |S| = angle X Y := by
    rw [show S = signedPlanarAngle (alignedHorizontal n X) (alignedHorizontal n Y) from rfl]
    rw [abs_signedPlanarAngle _ _
      (norm_pos_iff.mp (by rw [alignedHorizontal_norm unit up tX]; exact norm_pos_iff.mpr nX))
      (norm_pos_iff.mp (by rw [alignedHorizontal_norm unit up tY]; exact norm_pos_iff.mpr nY))]
    exact alignedHorizontal_angle unit up tX tY
  rw [K.horizontal_sectionDirection, K.horizontal_sectionDirection] at h
  change S - P = _ at h
  change _ = projectionHeadingError n Y - projectionHeadingError n X
  rw [← h, ← absS, ← absP]
  by_cases pos : 0 ≤ orient 0 x y
  · rw [if_pos pos, one_mul, abs_of_nonneg (sgn.mpr pos),
      abs_of_nonneg (sgnP.mpr pos)]
  · rw [if_neg pos, abs_of_neg (lt_of_not_ge (fun nonneg => pos (sgn.mp nonneg))),
      abs_of_neg (lt_of_not_ge (fun nonneg => pos (sgnP.mp nonneg)))]
    ring

/-- Changes of endpoint heading are at most the sum of the two small bend angles. -/
theorem abs_sectionHeadingError_sub_le (f : Face) {x y : Plane} (nx : x ≠ 0) (ny : y ≠ 0) :
    |K.sectionHeadingError f y - K.sectionHeadingError f x| ≤
      angle (K.sectionDirection f x) (K.sectionDirection f y) + angle x y := by
  rw [← K.signed_sectionAngle_sub_eq f nx ny, abs_mul]
  have sign : |(if 0 ≤ orient 0 x y then 1 else -1 : ℝ)| = 1 := by split <;> norm_num
  rw [sign, one_mul]
  exact (abs_sub _ _).trans_eq (by
    rw [abs_of_nonneg (angle_nonneg _ _), abs_of_nonneg (angle_nonneg _ _)])


end Unfoldings.ConvexRoof
