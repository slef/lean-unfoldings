module

public import Unfoldings.FewestNets.RevisedLatitudeAnnularShape
public import Unfoldings.FewestNets.RevisedLatitudeChartBudget
public import Unfoldings.FewestNets.LatitudeTriangleArea

/-! Put the short base north in the actual annular chart. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real Cap

/-- The two base vertices are symmetric. The third vertex is below them after reorientation. -/
structure AnnularChartData {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (i : AnnularTriangle a) where
  reorient : Plane ≃ₗᵢ[ℝ] Plane
  halfBase : ℝ
  base : ℝ
  apex : ℝ
  height : ℝ
  base_pos : 0 < halfBase
  height_pos : 0 < height
  selector_eq : reorient '' annularSlopeSelector positive small i =
    latitudeSlopeTriangle (-halfBase) halfBase base apex height
  base_lower : (if isPolarRow a (baseRow i) then 0.432 else 0.952) * spacing a <
    2 * halfBase * cos (rowStep a / 2)
  base_upper : 2 * halfBase < spacing a / 0.9612
  halfBase_bound : |halfBase| < widthFactor (isPolarRow a (baseRow i)) * spacing a /
    (2 * 0.9612)
  apex_bound : |apex| < spacing a / (2 * 0.9612)
  height_lower : heightDenominator (isPolarStrip a i.1.val) (relativeStep a) * radius a ≤
    0.9612 * height
  height_upper : height ≤ 2 * sin (rowStep a / 2) / 0.9612 +
    ordinateErrorFactor (isPolarStrip a i.1.val) * spacing a ^ 2 / radius a
  height_coarse_lower : (if isPolarStrip a i.1.val then 0.815 else 0.834) * radius a < height
  height_coarse_upper : height < (if isPolarStrip a i.1.val then 1.070 else 1.051) * radius a
  base_ordinate : |base| ≤ ordinateBound a (isPolarStrip a i.1.val)
  apex_ordinate : |base - height| ≤ ordinateBound a (isPolarStrip a i.1.val)
  horizontal_displacement : |apex| + |halfBase| ≤
    (if isPolarStrip a i.1.val then 0.8 else 1) * spacing a / 0.9612
  apex_label : exitHeadingChart false (reorient (annularSlopeVertex positive small i 2)) =
    ⟨apex, base - height⟩
  base_labels :
    let v k := exitHeadingChart false (reorient (annularSlopeVertex positive small i k))
    (v 0 = ⟨-halfBase, base⟩ ∧ v 1 = ⟨halfBase, base⟩) ∨
      (v 0 = ⟨halfBase, base⟩ ∧ v 1 = ⟨-halfBase, base⟩)

private theorem stripCount_one_lt {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    1 < stripCount a := by
  have lower := Nat.le_ceil ((π - 2 * AcuteLatitudeGrid.polarRadius a) / radius a)
  have fraction : 1 < (π - 2 * AcuteLatitudeGrid.polarRadius a) / radius a :=
    (lt_div_iff₀ (radius_pos positive)).mpr (by
      linarith only [radius_lt small, AcuteLatitudeGrid.polarRadius_lt small, pi_gt_d2])
  exact_mod_cast fraction.trans_le lower

private theorem widthFactors_eq {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (valid : j < stripCount a) :
    widthFactor (isPolarRow a j) + widthFactor (isPolarRow a (j + 1)) =
      2 * (if isPolarStrip a j then 0.8 else 1) := by
  have count := stripCount_one_lt positive small
  have not_both : ¬ ((j = 0 ∨ j = stripCount a) ∧ (j + 1 = 0 ∨ j + 1 = stripCount a)) := by
    rintro ⟨p | p, q | q⟩ <;> omega
  by_cases here : isPolarRow a j = true
  · have next : isPolarRow a (j + 1) = false := by
      apply Bool.eq_false_iff.mpr
      intro yes
      exact not_both ⟨of_decide_eq_true here, of_decide_eq_true yes⟩
    norm_num [isPolarStrip, here, next, widthFactor]
  · rw [Bool.eq_false_iff.mpr here]
    cases next : isPolarRow a (j + 1) <;>
      norm_num [isPolarStrip, Bool.eq_false_iff.mpr here, next, widthFactor]

/-- The actual selector admits the normalized chart used in the routing and count. -/
theorem exists_annularChartData {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (i : AnnularTriangle a) : Nonempty (AnnularChartData positive small i) := by
  obtain ⟨b, s, w, labels, rows, apex_near, hull, apex_label, base_labels⟩ :=
    exists_annularSlopeSelector_base positive small i
  let j := i.1.val
  let d := longitudeStep a b / 2
  let x := (slopeSite a j b d) 0
  let y := (slopeSite a j b d) 1
  let u := (slopeSite a j s w) 0
  let v := (slopeSite a j s w) 1
  let E : Plane ≃ₗᵢ[ℝ] Plane := if b = j then planeConjugation else LinearIsometryEquiv.refl ℝ Plane
  let ε : ℝ := if b = j then -1 else 1
  let H := ε * (y - v)
  have base_row : b = j ∨ b = j + 1 := rows.imp And.left And.left
  have apex_row : s = j ∨ s = j + 1 := by
    rcases rows with lower | upper
    · exact Or.inr lower.2
    · exact Or.inl upper.2
  have b_valid : b ≤ stripCount a := by
    rcases base_row with lower | upper
    · rw [lower]
      exact i.1.isLt.le
    · rw [upper]
      exact Nat.succ_le_of_lt i.1.isLt
  have d_pos : 0 < d := div_pos (longitudeStep_pos_lt_pi positive small b_valid).1 (by norm_num)
  have base_near : |d| ≤ longitudeStep a b / 2 := le_of_eq (abs_of_pos d_pos)
  have sb := slopeSite_bounds positive small i.1.isLt base_row base_near
  have sa := slopeSite_bounds positive small i.1.isLt apex_row apex_near
  have width := annular_base_width positive small i.1.isLt base_row
  change (if isPolarRow a b then 0.432 else 0.952) * spacing a <
    2 * x * cos (rowStep a / 2) ∧ 2 * x < spacing a / 0.9612 at width
  have cp : 0 < cos (rowStep a / 2) :=
    cos_pos_of_mem_Ioo ⟨by linarith only [rowStep_pos positive small, pi_pos],
      by linarith only [(rowStep_bounds positive small).2, radius_lt small, pi_gt_d2]⟩
  have coefficient : 0 < (if isPolarRow a b then 0.432 else 0.952 : ℝ) := by
    split_ifs <;> norm_num
  have x_pos : 0 < x := by
    have p := (mul_pos coefficient (spacing_pos positive)).trans width.1
    have q := pos_of_mul_pos_left p cp.le
    linarith only [q]
  have unscaled {k : ℕ} (w : ℝ) (bound : |(slopeSite a j k w) 0| <
      widthFactor (isPolarRow a k) * spacing a / (2 * 0.9612)) :
      |(slopeSite a j k w) 0| < spacing a / (2 * 0.9612) := by
    apply bound.trans_le
    apply div_le_div_of_nonneg_right _ (by norm_num)
    cases h : isPolarRow a k <;> simp only [h, widthFactor, Bool.false_eq_true, ite_false, ite_true] <;>
      linarith only [spacing_pos positive]

  have u_bound : |u| < spacing a / (2 * 0.9612) := unscaled w sa.2.2.1
  let polar := isPolarStrip a j
  have displacement : |u| + |x| ≤ (if polar then 0.8 else 1) * spacing a / 0.9612 := by
    have terms := add_le_add sa.2.2.1.le sb.2.2.1.le
    apply terms.trans_eq
    have eq : widthFactor (isPolarRow a b) + widthFactor (isPolarRow a s) =
        2 * (if polar then 0.8 else 1) := by
      have h := widthFactors_eq positive small i.1.isLt
      rcases rows with ⟨hb, hs⟩ | ⟨hb, hs⟩
      · rw [hb, hs]
        exact h
      · rw [hb, hs, add_comm]
        exact h
    rw [← add_div, ← add_mul, add_comm _ (widthFactor (isPolarRow a b)), eq]
    ring
  let error := ordinateErrorFactor polar * spacing a ^ 2 / radius a
  have geometry : (heightDenominator polar (relativeStep a) * radius a ≤ 0.9612 * H) ∧
      H ≤ 2 * sin (rowStep a / 2) / 0.9612 + error ∧
      (if polar then 0.815 else 0.834) * radius a < H ∧
      H < (if polar then 1.070 else 1.051) * radius a ∧
      |ε * y| ≤ ordinateBound a polar ∧ |ε * v| ≤ ordinateBound a polar := by
    have finish {Y₀ Y₁ : ℝ} (Y_bottom : Y₀ ≤ 0) (Y_top : 0 ≤ Y₁) (eq : H = Y₁ - Y₀)
        (lo : 2 * sin (rowStep a / 2) - error ≤ Y₁ - Y₀)
        (hi : Y₁ - Y₀ ≤ 2 * sin (rowStep a / 2) / 0.9612 + error)
        (bt : -Y₀ ≤ sin (rowStep a / 2) / 0.9612 + error)
        (tp : Y₁ ≤ sin (rowStep a / 2) / 0.9612 + error)
        (far : (if polar then 0.815 else 0.834) * radius a < Y₁ - Y₀)
        (close : Y₁ - Y₀ < (if polar then 1.070 else 1.051) * radius a) :
        (heightDenominator polar (relativeStep a) * radius a ≤ 0.9612 * H) ∧
        H ≤ 2 * sin (rowStep a / 2) / 0.9612 + error ∧
        (if polar then 0.815 else 0.834) * radius a < H ∧
      H < (if polar then 1.070 else 1.051) * radius a ∧
        |Y₀| ≤ ordinateBound a polar ∧ |Y₁| ≤ ordinateBound a polar := by
      obtain ⟨hl, _, ub, ut⟩ := affine_height_bounds positive small polar lo hi bt tp
      rw [eq, abs_of_nonpos Y_bottom, abs_of_nonneg Y_top]
      exact ⟨hl, hi, far, close, ub, ut⟩
    rcases rows with ⟨hb, hs⟩ | ⟨hb, hs⟩
    · change b = j at hb
      change s = j + 1 at hs
      have nb : |d| ≤ longitudeStep a j / 2 := by rw [← hb]; exact base_near
      have na : |w| ≤ longitudeStep a (j + 1) / 2 := by rw [← hs]; exact apex_near
      have H_eq : H = v - y := by simp [H, ε, hb]
      have ey : |ε * y| = |y| := by simp [ε, hb]
      have ev : |ε * v| = |v| := by simp [ε, hb]
      obtain ⟨⟨l, h⟩, ⟨_, bot⟩, _, top⟩ :=
        slopeSite_signed_heights positive small i.1.isLt nb na
      obtain ⟨⟨lower, upper⟩, ⟨yn, _⟩, vp, _⟩ :=
        slopeSite_pair_shape positive small i.1.isLt nb na
      have y_eq : y = (slopeSite a j j d) 1 := by simp only [y, hb]
      have v_eq : v = (slopeSite a j (j + 1) w) 1 := by simp only [v, hs]
      change y = (slopeSite a i.1.val i.1.val d) 1 at y_eq
      change v = (slopeSite a i.1.val (i.1.val + 1) w) 1 at v_eq
      simp only [← y_eq, ← v_eq] at l h bot top lower upper yn vp
      have nonneg : 0 ≤ (if polar then 0.393 else 0.412 : ℝ) * radius a :=
        mul_nonneg (by split_ifs <;> norm_num) (radius_pos positive).le
      rw [ey, ev]
      exact finish (by linarith only [yn, nonneg]) (nonneg.trans vp.le) H_eq l h bot top lower upper
    · change b = j + 1 at hb
      change s = j at hs
      have nb : |d| ≤ longitudeStep a (j + 1) / 2 := by rw [← hb]; exact base_near
      have na : |w| ≤ longitudeStep a j / 2 := by rw [← hs]; exact apex_near
      have different : b ≠ j := by omega
      have H_eq : H = y - v := by simp [H, ε, different]
      have ey : |ε * y| = |y| := by simp [ε, different]
      have ev : |ε * v| = |v| := by simp [ε, different]
      obtain ⟨⟨l, h⟩, ⟨_, bot⟩, _, top⟩ :=
        slopeSite_signed_heights positive small i.1.isLt na nb
      obtain ⟨⟨lower, upper⟩, ⟨vn, _⟩, yp, _⟩ :=
        slopeSite_pair_shape positive small i.1.isLt na nb
      have y_eq : y = (slopeSite a j (j + 1) d) 1 := by simp only [y, hb]
      have v_eq : v = (slopeSite a j j w) 1 := by simp only [v, hs]
      change y = (slopeSite a i.1.val (i.1.val + 1) d) 1 at y_eq
      change v = (slopeSite a i.1.val i.1.val w) 1 at v_eq
      simp only [← y_eq, ← v_eq] at l h bot top lower upper vn yp
      have nonneg : 0 ≤ (if polar then 0.393 else 0.412 : ℝ) * radius a :=
        mul_nonneg (by split_ifs <;> norm_num) (radius_pos positive).le
      obtain ⟨hl, hu, hlc, hh, vb, yb⟩ :=
        finish (by linarith only [vn, nonneg]) (nonneg.trans yp.le) H_eq l h bot top lower upper
      rw [ey, ev]
      exact ⟨hl, hu, hlc, hh, yb, vb⟩
  have Hp : 0 < H := by
    have p := mul_pos (heightDenominator_relativeStep_pos positive small polar) (radius_pos positive)
    linarith only [p.trans_le geometry.1]
  let frame := (exitHeadingChart false).toLinearEquiv.toLinearMap
  have at_re (p : Plane) : (exitHeadingChart false (E p)).re = p 0 := by
    simp only [exitHeadingChart_re, Bool.false_eq_true, ite_false, E]
    split_ifs <;> simp [planeConjugation_apply]
  have at_im (p : Plane) : (exitHeadingChart false (E p)).im = ε * p 1 := by
    simp only [exitHeadingChart_im, E, ε]
    split_ifs <;> simp [planeConjugation_apply]
  have minus_site : frame (E.toLinearEquiv.toLinearMap (slopeSite a j b (-d))) =
      ⟨-x, ε * y⟩ := by
    apply Complex.ext
    · rw [show frame (E.toLinearEquiv.toLinearMap (slopeSite a j b (-d))) =
        exitHeadingChart false (E (slopeSite a j b (-d))) from rfl, at_re]
      change (slopeSite a j b (-d)) 0 = -(slopeSite a j b d) 0
      simp [slopeSite, latitudeDenominator, sin_neg, cos_neg, neg_div]
    · rw [show frame (E.toLinearEquiv.toLinearMap (slopeSite a j b (-d))) =
        exitHeadingChart false (E (slopeSite a j b (-d))) from rfl, at_im]
      change ε * (slopeSite a j b (-d)) 1 = ε * (slopeSite a j b d) 1
      simp [slopeSite, latitudeDenominator, cos_neg]
  have plus_site : frame (E.toLinearEquiv.toLinearMap (slopeSite a j b d)) =
      ⟨x, ε * y⟩ := Complex.ext (at_re _) (at_im _)
  have apex_site : frame (E.toLinearEquiv.toLinearMap (slopeSite a j s w)) =
      ⟨u, ε * y - H⟩ := by
    apply Complex.ext (at_re _)
    change (exitHeadingChart false (E (slopeSite a j s w))).im = _
    rw [at_im]
    change ε * v = ε * y - H
    unfold H
    ring
  have reimage : E '' annularSlopeSelector positive small i = latitudeSlopeTriangle (-x) x (ε * y) u H := by
    have image : exitHeadingChart false '' (E '' annularSlopeSelector positive small i) =
        convexHull ℝ ({⟨u, ε * y - H⟩, ⟨-x, ε * y⟩, ⟨x, ε * y⟩} : Set ℂ) := by
      rw [hull]
      change frame '' (E.toLinearEquiv.toLinearMap '' convexHull ℝ _) = _
      rw [E.toLinearEquiv.toLinearMap.image_convexHull, frame.image_convexHull]
      simp only [Set.image_insert_eq, Set.image_singleton]
      rw [minus_site, plus_site, apex_site]
      congr 1
      ext p
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [latitudeSlopeTriangle, ← image, Set.preimage_image_eq _ (exitHeadingChart false).injective]
  have at_apex : exitHeadingChart false (E (annularSlopeVertex positive small i 2)) =
      ⟨u, ε * y - H⟩ := (congrArg (fun p => exitHeadingChart false (E p)) apex_label).trans apex_site
  have ordinates : |ε * y - H| ≤ ordinateBound a polar := by
    rw [show ε * y - H = ε * v by unfold H; ring]
    exact geometry.2.2.2.2.2
  have low_width := width.1
  rw [labels] at low_width
  have half_bound : |x| < widthFactor (isPolarRow a (baseRow i)) * spacing a / (2 * 0.9612) := by
    rw [← labels]
    exact sb.2.2.1
  refine ⟨⟨E, x, ε * y, u, H, x_pos, Hp, reimage, low_width, width.2, half_bound, u_bound,
    geometry.1, geometry.2.1, geometry.2.2.1, geometry.2.2.2.1, geometry.2.2.2.2.1, ordinates,
    displacement, at_apex, ?_⟩⟩
  let F (p : Plane) := exitHeadingChart false (E p)
  rcases base_labels with ⟨first, second⟩ | ⟨first, second⟩
  · exact Or.inl ⟨(congrArg F first).trans minus_site, (congrArg F second).trans plus_site⟩
  · exact Or.inr ⟨(congrArg F first).trans plus_site, (congrArg F second).trans minus_site⟩

end Unfoldings.FewestNets.RevisedLatitudeGrid
