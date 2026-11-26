module

public import Unfoldings.FewestNets.TightLatitudeBaseCharge

/-! The apex reciprocal sine on the analytic range of the acute count. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real InnerProductGeometry Cap

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) (analytic : a ≤ 0.31)
  {i : AnnularTriangle a} (D : AnnularChartData positive small i)

include analytic in
theorem spacing_le_of_analytic : spacing a ≤ 0.1581 * radius a := by
  have h : 0.51 * a ≤ 0.1581 := by linarith only [analytic]
  exact mul_le_mul_of_nonneg_right h (by unfold radius; positivity)

include analytic in
private theorem radius_le_of_analytic : radius a ≤ 0.401 := by
  unfold radius
  have h : 0.31 ≤ (0.401 / 0.72 : ℝ) ^ 2 := by norm_num
  have root := (sqrt_le_left (by norm_num : (0 : ℝ) ≤ 0.401 / 0.72)).mpr (analytic.trans h)
  linarith only [root]

include analytic in
private theorem chart_width_of_analytic :
    |D.apex| ≤ 0.08225 * radius a ∧ |D.halfBase| ≤ 0.08225 * radius a := by
  have cap : spacing a / (2 * 0.9612) ≤ 0.08225 * radius a := by
    apply (div_le_iff₀ (by norm_num)).mpr
    linarith only [spacing_le_of_analytic analytic, radius_pos positive]
  refine ⟨D.apex_bound.le.trans cap, ?_⟩
  rw [abs_of_pos D.base_pos]
  have h := D.base_upper
  ring_nf at h cap ⊢
  linarith only [h, cap]

include analytic in
private theorem apexLengthFactor_of_analytic : D.apexLengthFactor ≤ 1.021 := by
  apply D.apexLengthFactor_le_mean.trans
  obtain ⟨ha, hb⟩ := chart_width_of_analytic positive small analytic D
  have sa := pow_le_pow_left₀ (abs_nonneg _) ha 2
  have sb := pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [sq_abs] at sa sb
  have sh := pow_le_pow_left₀ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.815) (radius_pos positive).le) D.height_lower_coarse.le 2
  have prod : D.apex ^ 2 + D.halfBase ^ 2 ≤ 0.021 * D.height ^ 2 := by
    ring_nf at sa sb sh ⊢
    linarith only [sa, sb, sh, sq_nonneg (radius a)]
  have h := (div_le_iff₀ (pow_pos D.height_pos 2)).mpr prod
  linarith only [h]

include analytic in
private theorem chart_apex_height_of_analytic :
    1 / 1.026 ≤ gnomonicNormal (D.orientedVertex 2) 2 := by
  let p := D.orientedVertex 2
  let E := exitHeadingChart false
  have square : ‖p‖ ^ 2 = D.apex ^ 2 + (D.base - D.height) ^ 2 := by
    rw [← E.norm_map p]
    change ‖exitHeadingChart false (D.orientedVertex 2)‖ ^ 2 = _
    rw [AnnularChartData.orientedVertex, D.apex_label, Complex.sq_norm, Complex.normSq_apply]
    ring
  have ap := (chart_width_of_analytic positive small analytic D).1
  have y := D.apex_ordinate.trans (ordinate_coarse (i := i) positive small)
  have ap' := ap.trans (mul_le_mul_of_nonneg_left (radius_le_of_analytic analytic) (by norm_num))
  have y' := y.trans (mul_le_mul_of_nonneg_left (radius_le_of_analytic analytic) (by norm_num))
  have sa := pow_le_pow_left₀ (abs_nonneg _) ap' 2
  have sy := pow_le_pow_left₀ (abs_nonneg _) y' 2
  rw [sq_abs] at sa sy
  have nl : ‖northLift p‖ ≤ 1.026 := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp
    rw [horizontal_norm_sq, northLift_horizontal, northLift_height, one_pow, square]
    norm_num1 at sa sy ⊢
    linarith only [sa, sy]
  have hp : 0 < ‖northLift p‖ := norm_pos_iff.mpr (northLift_ne_zero p)
  change 1 / 1.026 ≤ gnomonicNormal p 2
  rw [gnomonicNormal, NormedSpace.normalize]
  change 1 / 1.026 ≤ ‖northLift p‖⁻¹ * (northLift p) 2
  rw [northLift_height, mul_one, ← one_div]
  exact one_div_le_one_div_of_le hp nl

/-- The three apex allowances distinguish the polar base and its neighboring strip. -/
def tightApexCoefficient (i : AnnularTriangle a) : ℝ :=
  if isPolarRow a (baseRow i) then 2.635 else if isPolarStrip a i.1.val then 1.196 else 1.168

theorem tightApexCoefficient_sub_pos (i : AnnularTriangle a) (small : a ≤ π / 6) :
    0 < tightApexCoefficient i - 0.089 * a := by
  unfold tightApexCoefficient
  split_ifs <;> linarith only [small, pi_lt_d6]

include analytic in
private theorem apex_height_budget_of_analytic :
    D.height * D.apexLengthFactor ≤ (tightApexCoefficient i - 0.089 * a) *
      (rowStep a / spacing a) * (2 * D.halfBase / 1.026) := by
  let B := 2 * D.halfBase
  let B₀ : ℝ := if isPolarRow a (baseRow i) then 0.432 else 0.952
  let S := (1 - 0.061 * a) / 0.9612 +
    ordinateErrorFactor (isPolarStrip a i.1.val) * 0.1581 ^ 2 / 0.852
  let c := tightApexCoefficient i - 0.089 * a
  let d := rowStep a
  let b := spacing a
  have bp : 0 < b := spacing_pos positive
  have Bp : 0 < B := mul_pos (by norm_num) D.base_pos
  have rn : 0 < B₀ * b := mul_pos (by dsimp only [B₀]; split_ifs <;> norm_num) bp
  have hc := apex_height_mul_cos_le positive small _ (spacing_le_of_analytic analytic) D.height_upper
  have hb : D.height * (B₀ * b) ≤ B * (d * S) := by
    calc
      _ ≤ D.height * (B * cos (d / 2)) := mul_le_mul_of_nonneg_left D.base_lower.le D.height_pos.le
      _ = B * (D.height * cos (d / 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc Bp.le
  have scalars : 1.021 * S ≤ c * (B₀ / 1.026) := by
    have card : isPolarRow a (baseRow i) = true → isPolarStrip a i.1.val = true := by
      intro h
      unfold baseRow at h
      unfold isPolarStrip
      split at h <;> simp [h]
    cases h₁ : isPolarStrip a i.1.val <;> cases h₂ : isPolarRow a (baseRow i)
    · norm_num [S, c, B₀, tightApexCoefficient, h₁, h₂, ordinateErrorFactor] <;> linarith only [positive, analytic]
    · exact (Bool.false_ne_true (h₁.symm.trans (card h₂))).elim
    · norm_num [S, c, B₀, tightApexCoefficient, h₁, h₂, ordinateErrorFactor] <;> linarith only [positive, analytic]
    · norm_num [S, c, B₀, tightApexCoefficient, h₁, h₂, ordinateErrorFactor] <;> linarith only [positive, analytic]
  have top : (D.height * D.apexLengthFactor) * (B₀ * b) ≤ (B * d) * (c * (B₀ / 1.026)) := by
    calc
      _ ≤ (D.height * 1.021) * (B₀ * b) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (apexLengthFactor_of_analytic positive small analytic D) D.height_pos.le) rn.le
      _ = 1.021 * (D.height * (B₀ * b)) := by ring
      _ ≤ 1.021 * (B * (d * S)) := mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = (B * d) * (1.021 * S) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left scalars (mul_nonneg Bp.le (rowStep_pos positive small).le)
  apply le_of_mul_le_mul_right _ rn
  change (D.height * D.apexLengthFactor) * (B₀ * b) ≤ (c * (d / b) * (B / 1.026)) * (B₀ * b)
  convert top using 1
  field_simp [bp.ne']

include positive small analytic in
/-- The reciprocal capped sine of the actual annular apex in the analytic range. -/
theorem annular_apex_reciprocal_le_of_analytic (i : AnnularTriangle a) :
    1 / sin (min (annularCornerAngle i 2) (π / 2)) ≤
      (tightApexCoefficient i - 0.089 * a) * (rowStep a / spacing a) := by
  obtain ⟨A⟩ := exists_annularChartData positive small i
  let W := A.orientedVertex
  let E := exitHeadingChart false
  let L : ℂ := ⟨-A.halfBase, A.base⟩
  let R : ℂ := ⟨A.halfBase, A.base⟩
  let P : ℂ := ⟨A.apex, A.base - A.height⟩
  let θ := angle (W 0 - W 2) (W 1 - W 2)
  have hp : E (W 2) = P := A.apex_label
  have hb : (E (W 0) = L ∧ E (W 1) = R) ∨ (E (W 0) = R ∧ E (W 1) = L) := A.base_labels
  have diff (k : Fin 3) (hk : k = 0 ∨ k = 1) : W k ≠ W 2 := by
    intro equal
    have h := congrArg (fun w => (E w).im) equal
    rw [hp] at h
    rcases hk with rfl | rfl <;> rcases hb with ⟨hl, hr⟩ | ⟨hl, hr⟩
    all_goals first | rw [hl] at h | rw [hr] at h
    all_goals change A.base = A.base - A.height at h
    all_goals linarith only [h, A.height_pos]
  have projection := sin_gnomonic_corner_ge (W 2) (W 0) (W 1) (diff 0 (Or.inl rfl)) (diff 1 (Or.inr rfl))
  have sph := A.oriented_cornerAngle 2
  change annularCornerAngle i 2 =
    angle (minorArcTangent (gnomonicNormal (W 2)) (gnomonicNormal (W 0)))
      (minorArcTangent (gnomonicNormal (W 2)) (gnomonicNormal (W 1))) at sph
  rw [← sph] at projection
  have low := chart_apex_height_of_analytic positive small analytic A
  have sine_nonneg : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi (angle_nonneg _ _) (angle_le_pi _ _)
  have capped : sin (annularCornerAngle i 2) ≤ sin (min (annularCornerAngle i 2) (π / 2)) := by
    rcases le_total (annularCornerAngle i 2) (π / 2) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, sin_pi_div_two]
      exact sin_le_one _
  have formula : sin θ = (2 * A.halfBase / A.height) / A.apexLengthFactor := by
    have angle_eq : θ = angle (E (W 0) - E (W 2)) (E (W 1) - E (W 2)) := by
      rw [← map_sub, ← map_sub]
      exact (E.toLinearIsometry.angle_map _ _).symm
    rw [angle_eq, hp]
    rcases hb with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · rw [hl, hr]
      exact planar_apex_sine A.base_pos A.height_pos
    · rw [hl, hr, angle_comm]
      exact planar_apex_sine A.base_pos A.height_pos
  have bound := (mul_le_mul_of_nonneg_right low sine_nonneg).trans (projection.trans capped)
  rw [formula] at bound
  have lo : (2 * A.halfBase / 1.026) / (A.height * A.apexLengthFactor) ≤
      sin (min (annularCornerAngle i 2) (π / 2)) := by
    convert bound using 1
    ring
  have numerator : 0 < 2 * A.halfBase / 1.026 := div_pos (mul_pos (by norm_num) A.base_pos) (by norm_num)
  have denominator := mul_pos A.height_pos A.apexLengthFactor_pos
  have pos := (div_pos numerator denominator).trans_le lo
  have maxBudget := apex_height_budget_of_analytic positive small analytic A
  apply (div_le_iff₀ pos).mpr
  have product := mul_le_mul_of_nonneg_left lo
    (mul_nonneg (tightApexCoefficient_sub_pos i small).le
      (div_nonneg (rowStep_pos positive small).le (spacing_pos positive).le))
  refine le_trans ?_ product
  rw [← mul_div_assoc]
  exact (le_div_iff₀ denominator).mpr (by simpa only [one_mul] using maxBudget)

end Unfoldings.FewestNets.RevisedLatitudeGrid
