module

public import Unfoldings.FewestNets.AcuteLatitudeAnnularShape
public import Unfoldings.FewestNets.LatitudeTriangleArea

/-! Put the actual short base to the north, retaining its metric and all chart bounds. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real Cap

/-- Every actual annular selector admits the chart used by the three-exit routing theorem. -/
theorem exists_annularRoutingChart {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (i : AnnularTriangle a) :
    ∃ (E : Plane ≃ₗᵢ[ℝ] Plane) (left right base apex H : ℝ),
      E '' annularSlopeSelector positive small i = latitudeSlopeTriangle left right base apex H ∧
      0.8 * spacing a < right - left ∧ right - left < 1.010 * spacing a ∧
      0.883 * radius a < H ∧ H < 1.052 * radius a ∧
      |latitudeEastRatio right apex H| < 1.144 * spacing a / radius a ∧
      |latitudeWestRatio left apex H| < 1.144 * spacing a / radius a ∧
      (∀ p ∈ latitudeSlopeTriangle left right base apex H, ‖p‖ ≤ tan (0.568 * radius a)) ∧
      let vertex (k : Fin 3) := exitHeadingChart false (E (annularSlopeVertex positive small i k))
      vertex 2 = ⟨apex, base - H⟩ ∧
        ((vertex 0 = ⟨left, base⟩ ∧ vertex 1 = ⟨right, base⟩) ∨
          (vertex 0 = ⟨right, base⟩ ∧ vertex 1 = ⟨left, base⟩)) := by
  obtain ⟨b, s, w, rows, apex_near, hull, apex_label, base_labels⟩ :=
    exists_annularSlopeSelector_base positive small i
  let j := i.1.val
  let ell := chartColatitude a j
  let d := longitudeStep a b / 2
  let x := chartX ell (colatitude a b) d
  let y := chartY ell (colatitude a b) d
  let u := chartX ell (colatitude a s) w
  let v := chartY ell (colatitude a s) w
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
  have base_site := chartSite_bounds positive small i.1.isLt base_row 0 d base_near
  have apex_site := chartSite_bounds positive small i.1.isLt apex_row 0 w apex_near
  have width : 0.8 * spacing a < 2 * x ∧ 2 * x < 1.010 * spacing a :=
    annular_chart_base_width positive small i.1.isLt base_row
  have base_x : |x| < 0.505 * spacing a := base_site.2.2.1
  have apex_x : |u| < 0.505 * spacing a := apex_site.2.2.1
  have altitude : 0.883 * radius a < H ∧ H < 1.052 * radius a := by
    rcases rows with ⟨at_b, at_s⟩ | ⟨at_b, at_s⟩
    · have base_bound : |d| ≤ longitudeStep a i.1.val / 2 := by
        rw [← show b = i.1.val from at_b]
        exact base_near
      have apex_bound : |w| ≤ longitudeStep a (i.1.val + 1) / 2 := by
        rw [← show s = i.1.val + 1 from at_s]
        exact apex_near
      have h := chartSite_height_bounds positive small i.1.isLt d w base_bound apex_bound
      change b = j at at_b
      change s = j + 1 at at_s
      change _ < chartY ell (colatitude a (j + 1)) w - chartY ell (colatitude a j) d ∧ _ at h
      have eq : H = chartY ell (colatitude a (j + 1)) w - chartY ell (colatitude a j) d := by
        simp [H, ε, y, v, at_b, at_s]
      rw [eq]
      exact h
    · have base_bound : |d| ≤ longitudeStep a (i.1.val + 1) / 2 := by
        rw [← show b = i.1.val + 1 from at_b]
        exact base_near
      have apex_bound : |w| ≤ longitudeStep a i.1.val / 2 := by
        rw [← show s = i.1.val from at_s]
        exact apex_near
      have h := chartSite_height_bounds positive small i.1.isLt w d apex_bound base_bound
      change b = j + 1 at at_b
      change s = j at at_s
      change _ < chartY ell (colatitude a (j + 1)) d - chartY ell (colatitude a j) w ∧ _ at h
      have eq : H = chartY ell (colatitude a (j + 1)) d - chartY ell (colatitude a j) w := by
        simp [H, ε, y, v, at_b, at_s]
      rw [eq]
      exact h
  have H_pos : 0 < H := (mul_pos (by norm_num) (radius_pos positive)).trans altitude.1
  let frame := (exitHeadingChart false).toLinearEquiv.toLinearMap
  have at_re (p : Plane) : (exitHeadingChart false (E p)).re = p 0 := by
    simp only [exitHeadingChart_re, Bool.false_eq_true, ite_false, E]
    split_ifs <;> simp [planeConjugation_apply]
  have at_im (p : Plane) : (exitHeadingChart false (E p)).im = ε * p 1 := by
    simp only [exitHeadingChart_im, E, ε]
    split_ifs <;> simp [planeConjugation_apply]
  have minus_site : frame (E.toLinearEquiv.toLinearMap (annularSlopePoint a j b (-d))) =
      ⟨-x, ε * y⟩ := by
    apply Complex.ext
    · rw [show frame (E.toLinearEquiv.toLinearMap (annularSlopePoint a j b (-d))) =
        exitHeadingChart false (E (annularSlopePoint a j b (-d))) from rfl, at_re]
      change chartX ell (colatitude a b) (-d) = -x
      exact chartX_neg _ _ _
    · rw [show frame (E.toLinearEquiv.toLinearMap (annularSlopePoint a j b (-d))) =
        exitHeadingChart false (E (annularSlopePoint a j b (-d))) from rfl, at_im]
      change ε * chartY ell (colatitude a b) (-d) = ε * y
      rw [chartY_neg]
  have plus_site : frame (E.toLinearEquiv.toLinearMap (annularSlopePoint a j b d)) =
      ⟨x, ε * y⟩ := Complex.ext (at_re _) (at_im _)
  have apex_site : frame (E.toLinearEquiv.toLinearMap (annularSlopePoint a j s w)) =
      ⟨u, ε * y - H⟩ := by
    apply Complex.ext (at_re _)
    change (exitHeadingChart false (E (annularSlopePoint a j s w))).im = _
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
  refine ⟨E, -x, x, ε * y, u, H, reimage, ?_, ?_, altitude.1, altitude.2, ?_, ?_, ?_, ?_⟩
  · linarith only [width.1]
  · linarith only [width.2]
  · rw [latitudeEastRatio, abs_div, abs_of_pos H_pos]
    exact chart_long_side_ratio (radius_pos positive) (spacing_pos positive)
      apex_x.le base_x.le altitude.1
  · rw [latitudeWestRatio, abs_div, abs_of_pos H_pos]
    exact chart_long_side_ratio (radius_pos positive) (spacing_pos positive)
      apex_x.le (by simpa only [abs_neg] using base_x.le) altitude.1
  · intro p hp
    rw [← reimage] at hp
    obtain ⟨q, member, rfl⟩ := hp
    rw [E.norm_map]
    exact annularSlopeSelector_radius positive small i q member
  · let F (p : Plane) := exitHeadingChart false (E p)
    have at_apex : F (annularSlopeVertex positive small i 2) = ⟨u, ε * y - H⟩ :=
      (congrArg F apex_label).trans apex_site
    refine ⟨at_apex, ?_⟩
    rcases base_labels with ⟨first, second⟩ | ⟨first, second⟩
    · exact Or.inl ⟨(congrArg F first).trans minus_site, (congrArg F second).trans plus_site⟩
    · exact Or.inr ⟨(congrArg F first).trans plus_site, (congrArg F second).trans minus_site⟩

end Unfoldings.FewestNets.AcuteLatitudeGrid
