module

public import Unfoldings.FewestNets.CheckedMeshCorner
public import Unfoldings.FewestNets.MeshChartFrame
public import Unfoldings.Geometry.GnomonicRadius
public import Mathlib.Analysis.InnerProductSpace.TwoDim

/-! Centered corner altitude and angle are independent of the spatial frame. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry Cap

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem meshGnomonic_map (L : Space ≃ₗᵢ[ℝ] Space) (u v : Space) :
    meshGnomonic (L u) (L v) = L (meshGnomonic u v) := by
  rw [meshGnomonic, meshGnomonic, L.inner_map_map, map_sub, map_smul]

theorem meshCornerAltitude_map (L : Space ≃ₗᵢ[ℝ] Space) (p q : Space) :
    meshCornerAltitude (L p) (L q) = meshCornerAltitude p q := by
  unfold meshCornerAltitude
  rw [← map_sub, L.norm_map]
  congr 1
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_spatialCross, norm_sq_spatialCross, L.norm_map, L.norm_map, L.inner_map_map]

theorem meshCornerCosine_map (L : Space ≃ₗᵢ[ℝ] Space) (p q : Space) :
    meshCornerCosine (L p) (L q) = meshCornerCosine p q := by
  rw [meshCornerCosine, meshCornerCosine, L.norm_map, L.norm_map, L.inner_map_map]

theorem meshGnomonic_normal_inner {u v : Space} (uu : ‖u‖ = 1)
    (height : inner ℝ u v ≠ 0) : inner ℝ u (meshGnomonic u v) = 0 := by
  rw [meshGnomonic, inner_sub_right, real_inner_smul_right, inv_mul_cancel₀ height,
    real_inner_self_eq_norm_sq, uu, one_pow, sub_self]

theorem centeredSlope_eq_horizontal_meshGnomonic {u : Space} (uu : ‖u‖ = 1) (v : Space) :
    centeredSlope u v = horizontal (northFrame u (meshGnomonic u v)) := by
  rw [meshGnomonic, map_sub, map_smul, northFrame_center u uu, map_sub, map_smul,
    northLift_horizontal, sub_zero, centeredSlope, northFrame_height u uu]

/-- The fixed-point certificate's spatial cross-product expression is the
altitude in the actual vertex-centered gnomonic chart. -/
theorem centeredSlope_altitude_eq {u v w : Space} (o : Orientation ℝ Plane (Fin 2))
    (uu : ‖u‖ = 1) (hv : inner ℝ u v ≠ 0) (hw : inner ℝ u w ≠ 0) :
    |o.areaForm (centeredSlope u v) (centeredSlope u w)| /
      ‖centeredSlope u w - centeredSlope u v‖ =
      meshCornerAltitude (meshGnomonic u v) (meshGnomonic u w) := by
  let L := northFrame u
  let p := L (meshGnomonic u v)
  let q := L (meshGnomonic u w)
  have pv : p 2 = 0 := (northFrame_height u uu _).trans (meshGnomonic_normal_inner uu hv)
  have qv : q 2 = 0 := (northFrame_height u uu _).trans (meshGnomonic_normal_inner uu hw)
  have norm_horiz {z : Space} (zv : z 2 = 0) : ‖horizontal z‖ = ‖z‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [zv, zero_pow (by decide : 2 ≠ 0), add_zero] using (horizontal_norm_sq z).symm
  rw [centeredSlope_eq_horizontal_meshGnomonic uu, centeredSlope_eq_horizontal_meshGnomonic uu,
    ← meshCornerAltitude_map L]
  change |o.areaForm (horizontal p) (horizontal q)| / ‖horizontal q - horizontal p‖ =
    meshCornerAltitude p q
  have diff_v : (q - p) 2 = 0 := by
    change q 2 - p 2 = 0
    rw [qv, pv, sub_zero]
  rw [← map_sub, norm_horiz diff_v, meshCornerAltitude]
  congr 1
  apply (sq_eq_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  have equation := o.inner_sq_add_areaForm_sq (horizontal p) (horizontal q)
  rw [norm_horiz pv, norm_horiz qv] at equation
  have inner := horizontal_inner p q
  rw [pv, zero_mul, add_zero] at inner
  rw [sq_abs, norm_sq_spatialCross, inner]
  linarith only [equation]

end Unfoldings.FewestNets
