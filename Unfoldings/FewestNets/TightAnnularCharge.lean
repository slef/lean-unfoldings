module

public import Unfoldings.FewestNets.RevisedLatitudeAnnularBoundaryMetric
public import Unfoldings.Geometry.SphericalTriangleGram
public import Unfoldings.Geometry.ArcsinShortSide

/-! Sound algebraic charge formula for the actual triangles checked by the interval verifier. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real InnerProductGeometry Module

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

local notation "std" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin 3) ℝ)

def annularSineSquared (i : AnnularTriangle a) (j : Fin 3) : ℝ :=
  sin (annularSideLength i j) ^ 2

def annularAbsDet (i : AnnularTriangle a) : ℝ :=
  |spatialRayDet ((rings a).annularVertices i 0) ((rings a).annularVertices i 1)
    ((rings a).annularVertices i 2)|

def shortSideRatio (squaredSine : ℝ) : ℝ := 1 + squaredSine / 6 + squaredSine ^ 2 / 10

def annularMaxSineSquared (i : AnnularTriangle a) : ℝ :=
  max (annularSineSquared i 0) (max (annularSineSquared i 1) (annularSineSquared i 2))

/-- Exact real expression bounded by the checked interval arithmetic. -/
def annularAlgebraicCharge (i : AnnularTriangle a) : ℝ :=
  max (2 / π * shortSideRatio (annularMaxSineSquared i) *
      ((∑ j : Fin 3, √(annularSineSquared i j * annularSineSquared i (j + 2))) / annularAbsDet i))
    ((∑ j : Fin 3, √(annularSineSquared i j) * shortSideRatio (annularSineSquared i j)) / (π * 0.115))

include positive small in
theorem annularAbsDet_pos (i : AnnularTriangle a) : 0 < annularAbsDet i := by
  let V := (rings a).annularVertices i
  have det : spatialRayDet (V 0) (V 1) (V 2) = (std).det V := by
    rw [Basis.det_apply, Matrix.det_fin_three]
    simp only [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
    unfold spatialRayDet
    ring
  exact abs_pos.mpr (det.trans_lt ((rings_oriented positive small).annular_negative i)).ne

include positive small in
private theorem side_sine_pos (i : AnnularTriangle a) (j : Fin 3) :
    0 < sin (annularSideLength i j) :=
  sin_pos_of_pos_of_lt_pi (annularSideLength_pos positive small i j)
    (by linarith only [(annular_metric_bounds positive small i).1 j, pi_gt_three])

include positive small in
private theorem sqrt_annularSineSquared (i : AnnularTriangle a) (j : Fin 3) :
    √(annularSineSquared i j) = sin (annularSideLength i j) := by
  rw [annularSineSquared, sqrt_sq (side_sine_pos positive small i j).le]

include positive small in
private theorem annular_corner_sine_mul_incidentSides (i : AnnularTriangle a) (j : Fin 3) :
    sin (annularCornerAngle i j) *
      (sin (annularSideLength i j) * sin (annularSideLength i (j + 2))) = annularAbsDet i := by
  let V := (rings a).annularVertices i
  have index : (j + 2) + 1 = j := by fin_cases j <;> rfl
  have right : angle (V j) (V (j + 2)) = annularSideLength i (j + 2) := by
    rw [annularSideLength, index]
    exact angle_comm _ _
  have h := sphericalCorner_sin_mul_sides (V j) (V (j + 1)) (V (j + 2))
    ((rings a).annularVertices_unit i j) ((rings a).annularVertices_unit i (j + 1))
    ((rings a).annularVertices_unit i (j + 2)) (side_sine_pos positive small i j)
    (right.symm ▸ side_sine_pos positive small i (j + 2))
  change sin (annularCornerAngle i j) * (sin (annularSideLength i j) * sin (angle (V j) (V (j + 2)))) =
      |spatialRayDet (V j) (V (j + 1)) (V (j + 2))| at h
  rw [right] at h
  have rotate : spatialRayDet (V j) (V (j + 1)) (V (j + 2)) = spatialRayDet (V 0) (V 1) (V 2) := by
    fin_cases j
    · rfl
    · change spatialRayDet (V 1) (V 2) (V 0) = _
      unfold spatialRayDet
      ring
    · change spatialRayDet (V 2) (V 0) (V 1) = _
      unfold spatialRayDet
      ring
  rwa [rotate] at h

include positive small in
private theorem cap_reciprocal_bound (i : AnnularTriangle a) (j : Fin 3) :
    1 / sin (min (annularCornerAngle i j) (π / 2)) ≤
      √(annularSineSquared i j * annularSineSquared i (j + 2)) / annularAbsDet i := by
  have h := annular_corner_sine_mul_incidentSides positive small i j
  have Dp := annularAbsDet_pos positive small i
  have sp : 0 < sin (annularCornerAngle i j) := by
    rw [← h] at Dp
    exact pos_of_mul_pos_left Dp (mul_nonneg (side_sine_pos positive small i j).le
      (side_sine_pos positive small i (j + 2)).le)
  have cap : sin (annularCornerAngle i j) ≤ sin (min (annularCornerAngle i j) (π / 2)) := by
    rcases le_total (annularCornerAngle i j) (π / 2) with l | r
    · rw [min_eq_left l]
    · rw [min_eq_right r, sin_pi_div_two]
      exact sin_le_one _
  refine (div_le_div_of_nonneg_left zero_le_one sp cap).trans_eq ?_
  rw [sqrt_mul (show 0 ≤ annularSineSquared i j from sq_nonneg _), sqrt_annularSineSquared positive small i j,
    sqrt_annularSineSquared positive small i (j + 2), ← h]
  field_simp [sp.ne', (side_sine_pos positive small i j).ne', (side_sine_pos positive small i (j + 2)).ne']

private theorem short_length_le_sine_ratio {l : ℝ} (lp : 0 < l) (bound : l ≤ 0.574) :
    l ≤ sin l * shortSideRatio (sin l ^ 2) := by
  have sp := sin_pos_of_pos_of_lt_pi lp (by linarith only [bound, pi_gt_three])
  have sn : sin l ≤ 0.574 := (sin_le lp.le).trans bound
  have exact_side : arcsin (sin l) = l :=
    arcsin_sin (by linarith only [lp, pi_pos]) (by linarith only [bound, pi_gt_three])
  have h := arcsin_le_short_side_polynomial sp.le sn
  rw [exact_side] at h
  convert h using 1
  unfold shortSideRatio
  ring

private theorem shortSideRatio_le_of_le {x y : ℝ} (x0 : 0 ≤ x) (xy : x ≤ y) :
    shortSideRatio x ≤ shortSideRatio y := by
  have h := pow_le_pow_left₀ x0 xy 2
  dsimp only [shortSideRatio]
  linarith only [xy, h]

include positive small in
/-- Both alternatives in the Crofton charge are bounded by the real
expression evaluated by the rational interval verifier. -/
theorem annular_raw_charge_le_algebraic (i : AnnularTriangle a) :
    max ((∑ j : Fin 3, (2 * annularLongestSide i / (π * sin (annularLongestSide i))) /
        sin (min (annularCornerAngle i j) (π / 2))))
      (annularPerimeter i / (π * 0.115)) ≤
        annularAlgebraicCharge i := by
  let l := annularLongestSide i
  let factor := 2 * l / (π * sin l)
  let sq := annularMaxSineSquared i
  have choice : ∃ j : Fin 3, l = annularSideLength i j := by
    let x := annularSideLength i 0
    let y := annularSideLength i 1
    let z := annularSideLength i 2
    change ∃ j, max x (max y z) = _
    rcases le_total x (max y z) with h | h
    · rcases le_total y z with hy | hz
      · exact ⟨2, by rw [max_eq_right h, max_eq_right hy]⟩
      · exact ⟨1, by rw [max_eq_right h, max_eq_left hz]⟩
    · exact ⟨0, max_eq_left h⟩
  obtain ⟨k, at_k⟩ := choice
  have by_side (j : Fin 3) : annularSineSquared i j ≤ sq := by
    fin_cases j
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have fp : 0 ≤ factor := by
    dsimp only [factor]
    rw [at_k]
    exact div_nonneg (by have := annularSideLength_pos positive small i k; positivity)
      (mul_nonneg pi_pos.le (side_sine_pos positive small i k).le)
  have fb : factor ≤ 2 / π * shortSideRatio sq := by
    dsimp only [factor]
    rw [at_k]
    let s := annularSideLength i k
    have h := short_length_le_sine_ratio (annularSideLength_pos positive small i k)
      ((annular_metric_bounds positive small i).1 k).le
    have sp := side_sine_pos positive small i k
    have osc : s / sin s ≤ shortSideRatio (annularSineSquared i k) := by
      exact (div_le_iff₀ sp).mpr (by simpa only [annularSineSquared, mul_comm] using h)
    calc
      _ = (2 / π) * (s / sin s) := by ring
      _ ≤ 2 / π * shortSideRatio sq :=
        mul_le_mul_of_nonneg_left (osc.trans (shortSideRatio_le_of_le (sq_nonneg _) (by_side k))) (by positivity)
  have diff (j : Fin 3) :
      annularSideLength i j ≤ √(annularSineSquared i j) * shortSideRatio (annularSineSquared i j) := by
    rw [sqrt_annularSineSquared positive small i j]
    exact short_length_le_sine_ratio (annularSideLength_pos positive small i j)
      ((annular_metric_bounds positive small i).1 j).le
  apply max_le_max
  · change (∑ j : Fin 3, factor / sin (min (annularCornerAngle i j) (π / 2))) ≤ _
    simp only [Finset.sum_div]
    calc
      _ = factor * (∑ j : Fin 3, 1 / sin (min (annularCornerAngle i j) (π / 2))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ _ := by
        apply mul_le_mul fb (Finset.sum_le_sum fun j _ => cap_reciprocal_bound positive small i j)
        · apply Finset.sum_nonneg
          intro j _
          apply div_nonneg zero_le_one
          exact sin_nonneg_of_nonneg_of_le_pi
            (le_min (angle_nonneg _ _) pi_div_two_pos.le)
            ((min_le_right _ _).trans (by linarith only [pi_pos]))
        · exact fp.trans fb
  · exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun j _ => diff j) (by positivity)

end Unfoldings.FewestNets.RevisedLatitudeGrid
