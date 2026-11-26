module

public import Unfoldings.FewestNets.TightAnnularCharge
public import Unfoldings.Geometry.JointGnomonicBaseCharge
public import Unfoldings.Cap.HorizontalChartIsometry

/-! The two actual base corners share the sharper quadratic allowance. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real InnerProductGeometry Cap

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) {i : AnnularTriangle a}
  (D : AnnularChartData positive small i)

include positive small in
theorem ordinate_coarse : ordinateBound a (isPolarStrip a i.1.val) ≤ 0.550 * radius a := by
  unfold ordinateBound
  rw [mul_comm (0.550 : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ (radius_pos positive).le
  have upper := div_le_div_of_nonneg_right (relativeStep_bounds positive small).2
    (show (0 : ℝ) ≤ 2 * 0.9612 by norm_num)
  cases isPolarStrip a i.1.val <;> norm_num [ordinateErrorFactor] at upper ⊢ <;> linarith only [upper]

theorem AnnularChartData.height_lower_coarse : 0.815 * radius a < D.height := by
  have h := D.height_coarse_lower
  cases pol : isPolarStrip a i.1.val <;> simp [pol] at h <;>
    linarith only [h, radius_pos positive]

private theorem cross_ordinate_le_one :
    |1 + D.base * (D.base - D.height)| ≤ 1 := by
  have v := ordinate_coarse (i := i) positive small
  have X := abs_le.mp (D.base_ordinate.trans v)
  have Y := abs_le.mp (D.apex_ordinate.trans v)
  have H := D.height_lower_coarse
  have left : 0 < D.base := by linarith only [Y.1, H, radius_pos positive]
  have right : D.base - D.height < 0 := by linarith only [X.2, H, radius_pos positive]
  have prod := mul_neg_of_pos_of_neg left right
  have x₁ : D.base ≤ 0.55 * 0.522 := by linarith only [X.2, radius_lt small]
  have y₁ : -(D.base - D.height) ≤ 0.55 * 0.522 := by linarith only [Y.1, radius_lt small]
  have h := mul_le_mul x₁ y₁ (neg_pos.mpr right).le (by norm_num : (0 : ℝ) ≤ 0.55 * 0.522)
  rw [abs_of_nonneg (by nlinarith only [h] : 0 ≤ 1 + D.base * (D.base - D.height))]
  linarith only [prod]

private theorem jointBase_ratio_le :
    (D.apex ^ 2 * (1 + D.base ^ 2) + D.halfBase ^ 2) / D.height ^ 2 ≤ 0.2212 * a ^ 2 := by
  have rpos := radius_pos positive
  have bpos := spacing_pos positive
  have ymin := D.base_ordinate.trans (ordinate_coarse (i := i) positive small)
  have xcap : |D.halfBase| ≤ spacing a / (2 * 0.9612) := by
    rw [abs_of_pos D.base_pos]
    have hu := D.base_upper
    ring_nf at hu ⊢
    linarith only [hu]
  have acap := D.apex_bound.le
  have ycap : |D.base| ≤ 0.550 * 0.522 := ymin.trans (mul_le_mul_of_nonneg_left (radius_lt small).le (by norm_num))
  have h0 := D.height_lower_coarse.le
  have ys : D.base ^ 2 ≤ (0.550 * 0.522 : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ycap 2
  have xs : D.halfBase ^ 2 ≤ (spacing a / (2 * 0.9612)) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) xcap 2
  have ap : D.apex ^ 2 ≤ (spacing a / (2 * 0.9612)) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) acap 2
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 0.815 * radius a) h0 2
  have a_mul := mul_le_mul ap (add_le_add_right ys 1)
    (by positivity : 0 ≤ 1 + D.base ^ 2) (sq_nonneg (spacing a / (2 * 0.9612)))
  have bound := add_le_add a_mul xs
  have numeric : (spacing a / (2 * 0.9612)) ^ 2 * (1 + (0.550 * 0.522 : ℝ) ^ 2) +
      (spacing a / (2 * 0.9612)) ^ 2 ≤ 0.2212 * a ^ 2 * (0.815 * radius a) ^ 2 := by
    unfold spacing
    have h : 0 ≤ a ^ 2 * radius a ^ 2 := by positivity
    ring_nf at h ⊢
    linarith only [h]
  exact (div_le_iff₀ (pow_pos D.height_pos 2)).mpr
    (bound.trans (numeric.trans (mul_le_mul_of_nonneg_left hs (by positivity))))

local notation "point" => fun x y : ℝ => (WithLp.toLp 2 ![x, y] : Plane)

section

variable {positive small}

def AnnularChartData.orientedVertex (j : Fin 3) : Plane :=
  D.reorient (annularSlopeVertex positive small i j)

private theorem coordinate_form (z : Plane) {x y : ℝ}
    (h : exitHeadingChart false z = ⟨x, y⟩) : z = point x y := by
  have hx := congrArg Complex.re h
  have hy := congrArg Complex.im h
  simp only [exitHeadingChart_re, Bool.false_eq_true, ite_false] at hx
  simp only [exitHeadingChart_im] at hy
  ext j
  fin_cases j
  · exact hx
  · exact hy

theorem AnnularChartData.oriented_apex :
    D.orientedVertex 2 = point D.apex (D.base - D.height) :=
  coordinate_form _ D.apex_label

theorem AnnularChartData.oriented_bases :
    let L := point (-D.halfBase) D.base
    let R := point D.halfBase D.base
    (D.orientedVertex 0 = L ∧ D.orientedVertex 1 = R) ∨
      (D.orientedVertex 0 = R ∧ D.orientedVertex 1 = L) :=
  D.base_labels.imp (fun h => ⟨coordinate_form _ h.1, coordinate_form _ h.2⟩)
    (fun h => ⟨coordinate_form _ h.1, coordinate_form _ h.2⟩)

theorem AnnularChartData.oriented_cornerAngle (j : Fin 3) :
    annularCornerAngle i j =
      angle (minorArcTangent (gnomonicNormal (D.orientedVertex j)) (gnomonicNormal (D.orientedVertex (j + 1))))
        (minorArcTangent (gnomonicNormal (D.orientedVertex j)) (gnomonicNormal (D.orientedVertex (j + 2)))) := by
  let T := (annularChartFrame a i).trans (horizontalChartIsometry D.reorient)
  have hom (k : Fin 3) : gnomonicNormal (D.orientedVertex k) = T ((rings a).annularVertices i k) := by
    unfold AnnularChartData.orientedVertex T
    rw [← horizontalChartIsometry_gnomonicNormal, gnomonicNormal_annularSlopeVertex]
    rfl
  have tangent (u v : Space) : T (minorArcTangent u v) = minorArcTangent (T u) (T v) := by
    unfold minorArcTangent
    have angles : angle (T u) (T v) = angle u v := T.toLinearIsometry.angle_map u v
    simp only [map_sub, map_smul, angles]
  rw [hom, hom, hom, ← tangent, ← tangent]
  exact (T.toLinearIsometry.angle_map _ _).symm

end

include positive small in
/-- The two actual spherical base corners have one joint reciprocal-sine bound. -/
theorem annular_joint_base_reciprocal_le (i : AnnularTriangle a) :
    1 / sin (min (annularCornerAngle i 0) (π / 2)) +
      1 / sin (min (annularCornerAngle i 1) (π / 2)) ≤ 2 + 0.2212 * a ^ 2 := by
  obtain ⟨E⟩ := exists_annularChartData positive small i
  let W := E.orientedVertex
  let Λ := point (-E.halfBase) E.base
  let Ρ := point E.halfBase E.base
  let Ω := point E.apex (E.base - E.height)
  have apex : W 2 = Ω := E.oriented_apex
  have labels : (W 0 = Λ ∧ W 1 = Ρ) ∨ (W 0 = Ρ ∧ W 1 = Λ) := E.oriented_bases
  let corner (x y : Plane) := angle (minorArcTangent (gnomonicNormal x) (gnomonicNormal y))
    (minorArcTangent (gnomonicNormal x) (gnomonicNormal Ω))
  let cot (θ : ℝ) := |cos θ| / sin θ
  have c0 : annularCornerAngle i 0 = corner (W 0) (W 1) := by
    rw [E.oriented_cornerAngle 0]
    change angle (minorArcTangent (gnomonicNormal (W 0)) (gnomonicNormal (W 1)))
      (minorArcTangent (gnomonicNormal (W 0)) (gnomonicNormal (W 2))) = _
    rw [apex]
  have c1 : annularCornerAngle i 1 = corner (W 1) (W 0) := by
    rw [E.oriented_cornerAngle 1]
    change angle (minorArcTangent (gnomonicNormal (W 1)) (gnomonicNormal (W 2)))
      (minorArcTangent (gnomonicNormal (W 1)) (gnomonicNormal (W 0))) = _
    rw [apex, angle_comm]
  have joint := joint_gnomonic_base_cotangent_bound E.halfBase E.base E.apex (E.base - E.height)
    E.base_pos (by linarith only [E.height_pos]) (cross_ordinate_le_one positive small E)
  change (cot (corner Λ Ρ) ^ 2 + cot (corner Ρ Λ) ^ 2) / 2 ≤ _ at joint
  have adjust : ((E.base - E.height) - E.base) ^ 2 = E.height ^ 2 := by ring
  rw [adjust] at joint
  have cost : (cot (annularCornerAngle i 0) ^ 2 + cot (annularCornerAngle i 1) ^ 2) / 2 ≤
      0.2212 * a ^ 2 := by
    rw [c0, c1]
    rcases labels with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [h0, h1]
      exact joint.trans (jointBase_ratio_le positive small E)
    · rw [h0, h1, add_comm]
      exact joint.trans (jointBase_ratio_le positive small E)
  have l := cappedReciprocalSine_le_cotangent (annular_corner_pos positive small i 0)
  have r := cappedReciprocalSine_le_cotangent (annular_corner_pos positive small i 1)
  change 1 / sin (min (annularCornerAngle i 0) (π / 2)) ≤ 1 + cot (annularCornerAngle i 0) ^ 2 / 2 at l
  change 1 / sin (min (annularCornerAngle i 1) (π / 2)) ≤ 1 + cot (annularCornerAngle i 1) ^ 2 / 2 at r
  linarith only [l, r, cost]

end Unfoldings.FewestNets.RevisedLatitudeGrid
