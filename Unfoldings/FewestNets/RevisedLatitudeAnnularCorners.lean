module

public import Unfoldings.FewestNets.RevisedLatitudePlanarCorners
public import Unfoldings.FewestNets.RevisedLatitudeCornerScalars
public import Unfoldings.Geometry.GnomonicCornerAngles

/-! The actual apex and base corners satisfy the revised crossing denominators. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real Cap InnerProductGeometry

variable {a : ℝ}

/-- The actual spherical corner made by the two minor arcs. -/
def annularCornerAngle (i : AnnularTriangle a) (j : Fin 3) : ℝ :=
  angle (minorArcTangent ((rings a).annularVertices i j) ((rings a).annularVertices i (j + 1)))
    (minorArcTangent ((rings a).annularVertices i j) ((rings a).annularVertices i (j + 2)))

/-- The coefficient for this triangle's apex in the uniform count. -/
def annularApexCoefficient (i : AnnularTriangle a) : ℝ :=
  apexCountCoefficient (isPolarStrip a i.1.val) (isPolarRow a (baseRow i))

set_option maxHeartbeats 1500000 in
/-- The capped-sine denominator at each corner of the actual annular triangle. -/
theorem annular_spherical_capped_sines (positive : 0 < a) (small : a ≤ π / 6)
    (i : AnnularTriangle a) :
    1 ≤ (annularApexCoefficient i - 0.073 * a) * (rowStep a / spacing a) *
      sin (min (annularCornerAngle i 2) (π / 2)) ∧
      ∀ j : Fin 3, j ≠ 2 → 0.932 < sin (min (annularCornerAngle i j) (π / 2)) := by
  obtain ⟨D⟩ := exists_annularChartData positive small i
  obtain ⟨φ, φp, φs, tilt_error, radius_bound⟩ := D.exists_tilt
  let V := annularSlopeVertex positive small i
  let T := annularChartFrame a i
  let E := D.reorient.trans (exitHeadingChart false)
  let Z j := E (V j)
  let θ (j : Fin 3) := angle (Z (j + 1) - Z j) (Z (j + 2) - Z j)
  have φlt : φ < π / 2 := by linarith only [φs, pi_gt_d2]
  have cos_p : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith only [φp, pi_pos], φlt⟩
  have cos_large : 0.955 ≤ cos φ := by
    have square := pow_le_pow_left₀ φp.le φs 2
    nlinarith only [square, one_sub_sq_div_two_le_cos (x := φ)]
  have spatial (j : Fin 3) : gnomonicNormal (V j) = T ((rings a).annularVertices i j) :=
    gnomonicNormal_annularSlopeVertex positive small i j
  have planar (j : Fin 3) : angle (V (j + 1) - V j) (V (j + 2) - V j) = θ j := by
    unfold θ Z
    rw [← map_sub, ← map_sub]
    exact (E.toLinearIsometry.angle_map _ _).symm
  have spherical (j : Fin 3) :
      angle (minorArcTangent (gnomonicNormal (V j)) (gnomonicNormal (V (j + 1))))
        (minorArcTangent (gnomonicNormal (V j)) (gnomonicNormal (V (j + 2)))) =
          annularCornerAngle i j := by
    have tang (u v : Space) :
        T (minorArcTangent u v) = minorArcTangent (T u) (T v) := by
      unfold minorArcTangent
      have angle_map : angle (T u) (T v) = angle u v := T.toLinearIsometry.angle_map _ _
      simp only [map_sub, map_smul, angle_map]
    rw [spatial, spatial, spatial, ← tang, ← tang]
    exact T.toLinearIsometry.angle_map _ _
  have injective : Function.Injective V := by
    intro j k same
    apply annularVertex_injective positive small i
    apply T.injective
    rw [← spatial, ← spatial, same]
  have height (j : Fin 3) : cos φ ≤ gnomonicNormal (V j) 2 := by
    have member : V j ∈ annularSlopeSelector positive small i := subset_convexHull ℝ _ ⟨j, rfl⟩
    have inside : D.reorient (V j) ∈ latitudeSlopeTriangle
        (-D.halfBase) D.halfBase D.base D.apex D.height :=
      D.selector_eq ▸ Set.mem_image_of_mem D.reorient member
    have bound := radius_bound _ inside
    rw [D.reorient.norm_map] at bound
    let P := SpatialPlane.ofGraph 0 (V j)
    have equal : gnomonicNormal (V j) = P.normal := by
      rw [← SpatialPlane.ofGraph_normalSlope 0 (V j)]
      exact gnomonicNormal_slope _ P.normal_unit P.normal_upward
    rw [equal]
    exact SpatialPlane.ofGraph_normal_height_of_slope_radius φp φlt 0 _ bound
  have projected (j : Fin 3) :
      0.955 * sin (θ j) ≤ sin (min (annularCornerAngle i j) (π / 2)) ∧
      |annularCornerAngle i j - θ j| ≤ 0.512 * φ ^ 2 := by
    have f : V (j + 1) ≠ V j := injective.ne (by fin_cases j <;> decide)
    have g : V (j + 2) ≠ V j := injective.ne (by fin_cases j <;> decide)
    have s := sin_gnomonic_corner_ge (V j) (V (j + 1)) (V (j + 2)) f g
    rw [spherical, planar] at s
    have tn : 0 ≤ sin (θ j) := sin_nonneg_of_nonneg_of_le_pi (angle_nonneg _ _) (angle_le_pi _ _)
    have cap : sin (annularCornerAngle i j) ≤ sin (min (annularCornerAngle i j) (π / 2)) := by
      rcases le_total (annularCornerAngle i j) (π / 2) with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h, sin_pi_div_two]
        exact sin_le_one _
    refine ⟨(mul_le_mul_of_nonneg_right (cos_large.trans (height j)) tn).trans (s.trans cap), ?_⟩
    have error := abs_gnomonic_corner_angle_sub_le (V j) (V (j + 1)) (V (j + 2)) f g cos_p (height j)
    rw [spherical, planar] at error
    exact error.trans (revised_projection_allowance_le_sq φp.le φs)
  let L : ℂ := ⟨-D.halfBase, D.base⟩
  let R : ℂ := ⟨D.halfBase, D.base⟩
  let A : ℂ := ⟨D.apex, D.base - D.height⟩
  have at_apex : Z 2 = A := D.apex_label
  have at_base : (Z 0 = L ∧ Z 1 = R) ∨ (Z 0 = R ∧ Z 1 = L) := D.base_labels
  have θ₀ : θ 0 = angle (Z 1 - Z 0) (Z 2 - Z 0) := rfl
  have θ₁ : θ 1 = angle (Z 2 - Z 1) (Z 0 - Z 1) := rfl
  have θ₂ : θ 2 = angle (Z 0 - Z 2) (Z 1 - Z 2) := rfl
  have apex_formula : sin (θ 2) = (2 * D.halfBase / D.height) / D.apexLengthFactor := by
    have formula := planar_apex_sine (b := D.base) (y := D.apex) D.base_pos D.height_pos
    rcases at_base with ⟨z₀, z₁⟩ | ⟨z₀, z₁⟩
    · rw [θ₂, z₀, z₁, at_apex]; exact formula
    · rw [θ₂, z₀, z₁, at_apex, angle_comm]; exact formula
  have base_error := planar_base_angles D
  have base_formula : |θ 0 - π / 2| ≤ arctan 0.335 ∧ |θ 1 - π / 2| ≤ arctan 0.335 := by
    rcases at_base with ⟨z₀, z₁⟩ | ⟨z₀, z₁⟩
    · rw [θ₀, θ₁, z₀, z₁, at_apex, angle_comm (A - R) (L - R)]; exact base_error
    · rw [θ₀, θ₁, z₀, z₁, at_apex, angle_comm (A - L) (R - L)]
      exact ⟨base_error.2, base_error.1⟩
  constructor
  · let width := 2 * D.halfBase
    let J := D.apexLengthFactor
    let coefficient := (annularApexCoefficient i - 0.073 * a) * (rowStep a / spacing a)
    have card : isPolarRow a (baseRow i) = true → isPolarStrip a i.1.val = true := by
      intro h
      unfold baseRow at h
      unfold isPolarStrip
      split at h <;> simp [h]
    have bp : 0 < width := mul_pos (by norm_num) D.base_pos
    have jp : 0 < J := D.apexLengthFactor_pos
    have width_budget := apex_height_to_sine_budget positive small _ _ card bp D.height_pos
      D.base_lower D.height_upper D.apexLengthFactor_le
    have s := (projected 2).1
    rw [apex_formula] at s
    have sine : 0.955 * width / (D.height * J) ≤ sin (min (annularCornerAngle i 2) (π / 2)) := by
      change 0.955 * (width / D.height / J) ≤ _ at s
      rw [div_div] at s
      simpa only [mul_div_assoc] using s
    have cp : 0 < coefficient :=
      mul_pos (apexCountCoefficient_pos small _ _) (div_pos (rowStep_pos positive small) (spacing_pos positive))
    have h : 1 ≤ coefficient * (0.955 * width / (D.height * J)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (mul_pos D.height_pos jp)).mpr
      rw [one_mul]
      change D.height * J ≤ coefficient * (0.955 * width) at width_budget
      exact width_budget
    exact h.trans (mul_le_mul_of_nonneg_left sine cp.le)
  · intro j different
    have planar_near : |θ j - π / 2| ≤ arctan 0.335 := by
      fin_cases j
      · exact base_formula.1
      · exact base_formula.2
      · exact (different rfl).elim
    have poly := arctan_le_fifth (show 0 ≤ (0.335 : ℝ) by norm_num)
    norm_num1 at poly
    have phi_sq := pow_le_pow_left₀ φp.le φs 2
    have lower : π / 2 - 0.3686 ≤ annularCornerAngle i j := by
      linarith only [(abs_le.mp (projected j).2).1, (abs_le.mp planar_near).1, poly, phi_sq]
    have sine := sin_le_sin_of_le_of_le_pi_div_two
      (show -(π / 2) ≤ π / 2 - 0.3686 by linarith only [pi_gt_d2])
      (min_le_right (annularCornerAngle i j) _) (le_min lower (by norm_num))
    rw [sin_pi_div_two_sub] at sine
    linarith only [sine, one_sub_sq_div_two_le_cos (x := (0.3686 : ℝ))]

end Unfoldings.FewestNets.RevisedLatitudeGrid
