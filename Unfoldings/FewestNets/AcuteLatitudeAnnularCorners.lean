module

public import Unfoldings.FewestNets.AcuteLatitudeChartAngles
public import Unfoldings.FewestNets.AcuteLatitudeCornerScalars
public import Unfoldings.Geometry.GnomonicCornerAngles

/-! Exact corner estimates for the actual annular spherical chord triangles. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Cap Module Real InnerProductGeometry

/-- The interior angle between the two actual minor arcs at a chord vertex. -/
def annularCornerAngle {a : ℝ} (i : AnnularTriangle a) (k : Fin 3) : ℝ :=
  angle (minorArcTangent (annularVertices a i k) (annularVertices a i (k + 1)))
    (minorArcTangent (annularVertices a i k) (annularVertices a i (k + 2)))

private theorem angle_linearIsometryEquiv {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
    (L : E ≃ₗᵢ[ℝ] F) (u v : E) : angle (L u) (L v) = angle u v :=
  L.toLinearIsometry.angle_map u v

private theorem minorArcTangent_linearIsometryEquiv (E : Space ≃ₗᵢ[ℝ] Space) (u v : Space) :
    E (minorArcTangent u v) = minorArcTangent (E u) (E v) := by
  simp only [minorArcTangent, map_smul, map_sub, angle_linearIsometryEquiv]

private theorem gnomonicNormal_annularSlopeVertex {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (i : AnnularTriangle a) (k : Fin 3) :
    gnomonicNormal (annularSlopeVertex positive small i k) =
      annularChartBasis positive small i k := by
  have unit : ‖annularChartBasis positive small i k‖ = 1 := by
    rw [annularChartBasis_apply, (annularChartFrame a i).norm_map, annularVertices_unit]
  have upward : 0 < annularChartBasis positive small i k 2 :=
    (by norm_num : (0 : ℝ) < 0.991).trans (annularChartBasis_height positive small i k)
  exact gnomonicNormal_slope _ unit upward

/-- The actual spherical corner half-sines have the distinct apex and base margins
used in the annular crossing estimate. -/
theorem annular_spherical_corner_halfSines {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (i : AnnularTriangle a) :
    0.334 * (spacing a / radius a) < sin (annularCornerAngle i 2 / 2) ∧
      ∀ j : Fin 3, j ≠ 2 → 0.564 < sin (annularCornerAngle i j / 2) := by
  let V := annularSlopeVertex positive small i
  let θ (j : Fin 3) := angle (V (j + 1) - V j) (V (j + 2) - V j)
  have lift (j : Fin 3) : gnomonicNormal (V j) = annularChartFrame a i (annularVertices a i j) :=
    (gnomonicNormal_annularSlopeVertex positive small i j).trans (annularChartBasis_apply positive small i j)
  have injective : Function.Injective V := by
    intro j k equal
    apply (annularChartBasis positive small i).injective
    exact (gnomonicNormal_annularSlopeVertex positive small i j).symm.trans
      ((congrArg gnomonicNormal equal).trans (gnomonicNormal_annularSlopeVertex positive small i k))
  have distortion (j : Fin 3) : 0.982 * sin (θ j / 2) ≤ sin (annularCornerAngle i j / 2) := by
    have first : j + 1 ≠ j := by fin_cases j <;> decide
    have second : j + 2 ≠ j := by fin_cases j <;> decide
    have comparison := sin_half_gnomonic_corner_ge (V j) (V (j + 1)) (V (j + 2))
      (injective.ne first) (injective.ne second)
    have height : 0.982 ≤ gnomonicNormal (V j) 2 := by
      rw [gnomonicNormal_annularSlopeVertex positive small i j]
      exact (by norm_num : (0.982 : ℝ) ≤ 0.991).trans (annularChartBasis_height positive small i j).le
    have θ_le : θ j ≤ π := angle_le_pi _ _
    have sine : 0 ≤ sin (θ j / 2) := sin_nonneg_of_nonneg_of_le_pi
      (div_nonneg (angle_nonneg _ _) (by norm_num)) (by linarith only [θ_le, pi_pos])
    have lower := (mul_le_mul_of_nonneg_right height sine).trans comparison
    simpa only [lift, ← minorArcTangent_linearIsometryEquiv, angle_linearIsometryEquiv,
      annularCornerAngle] using lower
  obtain ⟨E, left, right, base, apex, H, _, width, _, altitude, height, east, west, _, at_apex, at_base⟩ :=
    exists_annularRoutingChart positive small i
  let frame := E.trans (exitHeadingChart false)
  let Z (j : Fin 3) := frame (V j)
  have planar (j : Fin 3) : θ j = angle (Z (j + 1) - Z j) (Z (j + 2) - Z j) := by
    unfold θ Z
    rw [← map_sub, ← map_sub, angle_linearIsometryEquiv]
  let L : ℂ := ⟨left, base⟩
  let R : ℂ := ⟨right, base⟩
  let A : ℂ := ⟨apex, base - H⟩
  have apex_name : Z 2 = A := at_apex
  have base_names : (Z 0 = L ∧ Z 1 = R) ∨ (Z 0 = R ∧ Z 1 = L) := at_base
  have H_pos : 0 < H := (mul_pos (by norm_num) (radius_pos positive)).trans altitude
  have base_pos : left < right :=
    sub_pos.mp ((mul_pos (by norm_num) (spacing_pos positive)).trans width)
  let x := spacing a / radius a
  have x_pos : 0 < x := div_pos (spacing_pos positive) (radius_pos positive)
  have ratio : x = 0.56 * a := by
    dsimp [x, spacing]
    field_simp [(radius_pos positive).ne']
  have small_a : a < 0.524 := by linarith only [small, pi_lt_d6]
  have x_small : x ≤ 0.294 := by rw [ratio]; linarith only [small_a]
  have long_bound : 1.144 * spacing a / radius a < 0.338 := by
    rw [mul_div_assoc]
    change 1.144 * x < 0.338
    rw [ratio]
    linarith only [small_a]
  have apex_lower : 0.682 * x < angle (R - A) (L - A) :=
    latitude_apex_lower positive small H_pos width height east west
  have lower_base := latitude_base_halfSines (base := base) base_pos H_pos
    (east.trans long_bound).le (west.trans long_bound).le
  have θ₀ : θ 0 = angle (Z 1 - Z 0) (Z 2 - Z 0) := planar 0
  have θ₁ : θ 1 = angle (Z 2 - Z 1) (Z 0 - Z 1) := planar 1
  have θ₂ : θ 2 = angle (Z 0 - Z 2) (Z 1 - Z 2) := planar 2
  have apex_angle : 0.682 * x ≤ θ 2 := by
    rcases base_names with ⟨z₀, z₁⟩ | ⟨z₀, z₁⟩
    · rw [θ₂, z₀, z₁, apex_name, angle_comm]
      exact apex_lower.le
    · rw [θ₂, z₀, z₁, apex_name]
      exact apex_lower.le
  have base_angles : (0.564 < 0.982 * sin (θ 0 / 2)) ∧ (0.564 < 0.982 * sin (θ 1 / 2)) := by
    rcases base_names with ⟨z₀, z₁⟩ | ⟨z₀, z₁⟩
    · rw [θ₀, θ₁, z₀, z₁, apex_name, angle_comm (A - R) (L - R)]
      exact lower_base
    · rw [θ₀, θ₁, z₀, z₁, apex_name, angle_comm (A - L) (R - L)]
      exact ⟨lower_base.2, lower_base.1⟩
  refine ⟨(annular_apex_halfSine_of_angle x_pos x_small apex_angle
    (angle_le_pi _ _)).trans_le (distortion 2), ?_⟩
  intro j not_apex
  fin_cases j
  · exact base_angles.1.trans_le (distortion 0)
  · exact base_angles.2.trans_le (distortion 1)
  · exact (not_apex rfl).elim

/-- The actual capped-sine denominators in the annular crossing estimate. -/
theorem annular_spherical_capped_sines {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (i : AnnularTriangle a) :
    0.664 * (spacing a / radius a) < sin (min (annularCornerAngle i 2) (π / 2)) ∧
      ∀ j : Fin 3, j ≠ 2 → 0.93 < sin (min (annularCornerAngle i j) (π / 2)) := by
  obtain ⟨apex, base⟩ := annular_spherical_corner_halfSines positive small i
  have ratio : spacing a / radius a = 0.56 * a := by
    unfold spacing
    field_simp [(radius_pos positive).ne']
  have x_small : spacing a / radius a ≤ 0.294 := by
    rw [ratio]
    linarith only [small, pi_lt_d6]
  exact ⟨tri_apex_capped_sine (angle_nonneg _ _) (angle_le_pi _ _)
    (div_pos (spacing_pos positive) (radius_pos positive)) x_small apex.le,
    fun j different => tri_base_capped_sine (angle_nonneg _ _) (angle_le_pi _ _) (base j different).le⟩

end Unfoldings.FewestNets.AcuteLatitudeGrid
