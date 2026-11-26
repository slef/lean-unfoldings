module

public import Unfoldings.FewestNets.RevisedLatitudeAnnularBudget
public import Unfoldings.Geometry.GnomonicArcLength
public import Unfoldings.Geometry.ArctanScalars

/-! The three literal sides admit the sharpened length and perimeter bounds. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real InnerProductGeometry Cap

variable {a : ℝ} {positive : 0 < a} {small : a ≤ π / 6} {i : AnnularTriangle a}
  (D : AnnularChartData positive small i)

theorem AnnularChartData.displacement_small :
    |D.apex| + |D.halfBase| < 0.335 * D.height := by
  have hh := D.height_coarse_lower
  have uu := D.horizontal_displacement
  have xx := spacing_lt positive small
  have rr := radius_pos positive
  cases pol : isPolarStrip a i.1.val <;>
    simp only [pol, Bool.false_eq_true, ite_false, ite_true] at hh uu <;>
    ring_nf at hh uu ⊢ <;> linarith only [hh, uu, xx, rr]

/-- The actual chord basis projects back to the unit spherical sites. -/
theorem gnomonicNormal_annularSlopeVertex (positive : 0 < a) (small : a ≤ π / 6)
    (i : AnnularTriangle a) (j : Fin 3) :
    gnomonicNormal (annularSlopeVertex positive small i j) =
      annularChartFrame a i ((rings a).annularVertices i j) := by
  rw [← annularChartBasis_apply positive small]
  have unit : ‖annularChartBasis positive small i j‖ = 1 := by
    rw [annularChartBasis_apply, (annularChartFrame a i).norm_map]
    exact (rings a).annularVertices_unit i j
  exact gnomonicNormal_slope _ unit
    ((by norm_num : (0 : ℝ) < 0.9612).trans (annularChartBasis_height positive small i j))

theorem annularVertex_injective (positive : 0 < a) (small : a ≤ π / 6)
    (i : AnnularTriangle a) :
    Function.Injective ((rings a).annularVertices i) := by
  intro j k equal
  apply (annularChartBasis positive small i).injective
  rw [annularChartBasis_apply, annularChartBasis_apply, equal]

/-- The minor-arc length of an actual spherical triangle side. -/
def annularSideLength (i : AnnularTriangle a) (j : Fin 3) : ℝ :=
  angle ((rings a).annularVertices i j) ((rings a).annularVertices i (j + 1))

/-- The longest side of the original spherical chord triangle. -/
def annularLongestSide (i : AnnularTriangle a) : ℝ :=
  max (annularSideLength i 0) (max (annularSideLength i 1) (annularSideLength i 2))

/-- The perimeter counts each of the three actual spherical sides once. -/
def annularPerimeter (i : AnnularTriangle a) : ℝ := ∑ j : Fin 3, annularSideLength i j

theorem annularSideLength_pos (positive : 0 < a) (small : a ≤ π / 6)
    (i : AnnularTriangle a) (j : Fin 3) : 0 < annularSideLength i j := by
  let u := (rings a).annularVertices i j
  let v := (rings a).annularVertices i (j + 1)
  have different : u ≠ v := (annularVertex_injective positive small i).ne (by fin_cases j <;> decide)
  change 0 < angle u v
  refine lt_of_le_of_ne (angle_nonneg _ _) ?_
  intro zero
  obtain ⟨_, t, positive_t, scale⟩ := angle_eq_zero_iff.mp zero.symm
  have norm := congrArg (fun z : Space => ‖z‖) scale
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos positive_t,
    show ‖u‖ = 1 from (rings a).annularVertices_unit i j,
    show ‖v‖ = 1 from (rings a).annularVertices_unit i (j + 1), mul_one] at norm
  exact different ((by rw [scale, ← norm, one_smul] : v = u).symm)

private theorem complex_norm_le_of_ratio (u v : ℂ) (H : ℝ) (Hp : 0 < H)
    (re : |(u - v).re| ≤ 0.335 * H) (im : |(u - v).im| = H) :
    ‖u - v‖ ≤ 1.055 * H := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hh := pow_le_pow_left₀ (abs_nonneg _) re 2
  rw [sq_abs] at hh
  have vv := congrArg (fun x : ℝ => x ^ 2) im
  rw [sq_abs] at vv
  nlinarith only [hh, vv, sq_nonneg H]

private theorem AnnularChartData.chart_side_bounds :
    let W j := D.reorient (annularSlopeVertex positive small i j)
    (∀ j : Fin 3, ‖W j - W (j + 1)‖ < 0.590) ∧
    ∑ j : Fin 3, ‖W j - W (j + 1)‖ ≤ 2.54 * radius a := by
  let W j := D.reorient (annularSlopeVertex positive small i j)
  let Z j := exitHeadingChart false (W j)
  let L : ℂ := ⟨-D.halfBase, D.base⟩
  let R : ℂ := ⟨D.halfBase, D.base⟩
  let A : ℂ := ⟨D.apex, D.base - D.height⟩
  let H := D.height
  have baseline : ‖L - R‖ = 2 * D.halfBase := by
    have eq : L - R = ((-2 * D.halfBase : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [L, R] <;> ring
    rw [eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith only [D.base_pos])]
    ring
  have re_left : |(A - L).re| ≤ 0.335 * H := by
    change |D.apex - (-D.halfBase)| ≤ _
    rw [sub_neg_eq_add]
    exact ((abs_add_le _ _).trans D.displacement_small.le)
  have re_right : |(A - R).re| ≤ 0.335 * H :=
    (abs_sub _ _).trans D.displacement_small.le
  have im (v : ℂ) (at_top : v.im = D.base) : |(A - v).im| = H := by
    rw [Complex.sub_im, at_top]
    change |D.base - H - D.base| = H
    rw [show D.base - H - D.base = -H by ring, abs_neg, abs_of_pos D.height_pos]
  have l := complex_norm_le_of_ratio A L H D.height_pos re_left (im L rfl)
  have r := complex_norm_le_of_ratio A R H D.height_pos re_right (im R rfl)
  have hl : H < 1.070 * radius a := by
    have hh := D.height_coarse_upper
    cases h : isPolarStrip a i.1.val <;> simp [h] at hh <;>
      linarith only [hh, radius_pos positive]
  have bshort : ‖L - R‖ ≤ spacing a / 0.9612 := baseline.trans_le D.base_upper.le
  have long_small : 1.055 * H < 0.590 := by
    linarith only [hl, radius_lt small]
  have base_small : spacing a / 0.9612 < 0.590 := by
    apply (div_lt_iff₀ (by norm_num)).mpr
    linarith only [spacing_lt positive small, radius_lt small]
  have perimeter : spacing a / 0.9612 + 2 * (1.055 * H) ≤ 2.54 * radius a := by
    have b := spacing_lt positive small
    ring_nf at b hl ⊢
    linarith only [b, hl, radius_pos positive]
  have zm (j k : Fin 3) : ‖Z j - Z k‖ = ‖W j - W k‖ := by
    change ‖exitHeadingChart false (W j) - exitHeadingChart false (W k)‖ = _
    rw [← map_sub, LinearIsometryEquiv.norm_map]
  have az : Z 2 = A := D.apex_label
  have bz : (Z 0 = L ∧ Z 1 = R) ∨ (Z 0 = R ∧ Z 1 = L) := D.base_labels
  change (∀ j : Fin 3, ‖W j - W (j + 1)‖ < 0.590) ∧
    ∑ j : Fin 3, ‖W j - W (j + 1)‖ ≤ 2.54 * radius a
  simp_rw [← zm]
  rw [Fin.sum_univ_three]
  rcases bz with ⟨b0, b1⟩ | ⟨b0, b1⟩
  · refine ⟨fun j => ?_, ?_⟩
    · fin_cases j
      · change ‖Z 0 - Z 1‖ < _
        rw [b0, b1]
        exact bshort.trans_lt base_small
      · change ‖Z 1 - Z 2‖ < _
        rw [b1, az, norm_sub_rev]
        exact r.trans_lt long_small
      · change ‖Z 2 - Z 0‖ < _
        rw [az, b0]
        exact l.trans_lt long_small
    · change ‖Z 0 - Z 1‖ + ‖Z 1 - Z 2‖ + ‖Z 2 - Z 0‖ ≤ _
      rw [b0, b1, az, norm_sub_rev R A]
      exact (add_le_add (add_le_add bshort r) l).trans (by linarith only [perimeter])
  · refine ⟨fun j => ?_, ?_⟩
    · fin_cases j
      · change ‖Z 0 - Z 1‖ < _
        rw [b0, b1, norm_sub_rev]
        exact bshort.trans_lt base_small
      · change ‖Z 1 - Z 2‖ < _
        rw [b1, az, norm_sub_rev]
        exact l.trans_lt long_small
      · change ‖Z 2 - Z 0‖ < _
        rw [az, b0]
        exact r.trans_lt long_small
    · change ‖Z 0 - Z 1‖ + ‖Z 1 - Z 2‖ + ‖Z 2 - Z 0‖ ≤ _
      rw [b0, b1, az, norm_sub_rev R L, norm_sub_rev L A]
      exact (add_le_add (add_le_add bshort l) r).trans (by linarith only [perimeter])

/-- On the literal minor arcs the refined bound is 0.574 for each side and 2.54r in total. -/
theorem annular_metric_bounds (positive : 0 < a) (small : a ≤ π / 6)
    (i : AnnularTriangle a) :
    (∀ j : Fin 3, annularSideLength i j < 0.574) ∧ annularPerimeter i ≤ 2.54 * radius a := by
  obtain ⟨D⟩ := exists_annularChartData positive small i
  let V j := annularSlopeVertex positive small i j
  let W j := D.reorient (V j)
  have (j k : Fin 3) : ‖W j - W k‖ = ‖V j - V k‖ := by
    change ‖D.reorient (V j) - D.reorient (V k)‖ = _
    rw [← map_sub, LinearIsometryEquiv.norm_map]
  have arcs (j : Fin 3) : annularSideLength i j = angle (gnomonicNormal (V j)) (gnomonicNormal (V (j + 1))) := by
    unfold V annularSideLength
    rw [gnomonicNormal_annularSlopeVertex, gnomonicNormal_annularSlopeVertex]
    exact ((annularChartFrame a i).toLinearIsometry.angle_map _ _).symm
  obtain ⟨short, sum⟩ := D.chart_side_bounds
  have norm_eq (j : Fin 3) : ‖W j - W (j + 1)‖ = ‖V j - V (j + 1)‖ := this j (j + 1)
  refine ⟨fun j => ?_, ?_⟩
  · rw [arcs]
    have h := short j
    rw [norm_eq] at h
    have arc := angle_gnomonicNormal_le_centered (V j) (V (j + 1)) (by linarith only [h])
    have t := arctan_mono (show ‖V j - V (j + 1)‖ / 2 ≤ 0.295 by linarith only [h])
    have poly := arctan_le_fifth (show 0 ≤ (0.295 : ℝ) by norm_num)
    norm_num1 at poly
    linarith only [arc, t, poly]
  · unfold annularPerimeter
    apply le_trans _ sum
    apply Finset.sum_le_sum
    intro j _
    rw [arcs, norm_eq, ← dist_eq_norm]
    exact angle_gnomonicNormal_le_dist _ _

theorem annular_longestSide_factor (positive : 0 < a) (small : a ≤ π / 6)
    (i : AnnularTriangle a) :
    0 < 2 * annularLongestSide i / (π * sin (annularLongestSide i)) ∧
      2 * annularLongestSide i / (π * sin (annularLongestSide i)) ≤ 0.674 := by
  let l := annularLongestSide i
  have lp : 0 < l := (annularSideLength_pos positive small i 0).trans_le (le_max_left _ _)
  have bound := (annular_metric_bounds positive small i).1
  have upper : l < 0.574 := max_lt (bound 0) (max_lt (bound 1) (bound 2))
  have sp := sin_pos_of_pos_of_lt_pi lp (by linarith only [upper, pi_gt_three])
  have den := mul_pos pi_pos sp
  refine ⟨div_pos (mul_pos (by norm_num) lp) den, (div_le_iff₀ den).mpr ?_⟩
  have sq := pow_le_pow_left₀ lp.le upper.le 2
  have cube : l ^ 3 ≤ 0.574 ^ 2 * l := by nlinarith only [mul_le_mul_of_nonneg_right sq lp.le]
  have pi := mul_le_mul_of_nonneg_right pi_gt_d4.le sp.le
  have sn := sin_gt_sub_cube lp
  norm_num1 at sn pi cube ⊢
  linarith only [pi, sn, cube, lp]

end Unfoldings.FewestNets.RevisedLatitudeGrid
