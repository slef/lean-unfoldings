module

public import Unfoldings.Geometry.SphericalArcFrame
public import Unfoldings.Geometry.FiniteArcCrofton
public import Unfoldings.Geometry.MinorArcConnectivity
public import Unfoldings.Cone.SectorClosed

/-! The phase ball represents the actual closed minor arc between its endpoints. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialRotation

open InnerProductGeometry

theorem equatorPhase_mem_closedBall_iff {r θ : ℝ}
    (hθ : |θ| ≤ Real.pi) :
    (θ : EquatorPhase) ∈ Metric.closedBall 0 r ↔ θ ∈ Set.Icc (-r) r := by
  have period : 0 < (2 * Real.pi : ℝ) := by positivity
  have norm_phase :=
    (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) (x := θ) period.ne').mpr
      (by rwa [abs_of_pos period, mul_div_cancel_left₀ _ two_ne_zero])
  rw [Metric.mem_closedBall, dist_zero_right, norm_phase]
  exact abs_le

private theorem eq_polar_of_equatorialArc {r : ℝ} {x : Space}
    (mem : x ∈ equatorialArc r) :
    ∃ θ ∈ Set.Icc (-r) r, x = complexLift (polarRay θ) := by
  obtain ⟨phase, present, rfl⟩ := mem
  let θ := AddCircle.equivIco (2 * Real.pi) (-Real.pi) phase
  have representative : ((θ : ℝ) : EquatorPhase) = phase := AddCircle.coe_equivIco
  have bound : |(θ : ℝ)| ≤ Real.pi := abs_le.mpr ⟨θ.property.1, by linarith [θ.property.2]⟩
  refine ⟨θ, (equatorPhase_mem_closedBall_iff bound).mp (representative.symm ▸ present), ?_⟩
  rw [← representative, equatorPoint_coe_eq_complexLift]

private theorem complexLift_polarRay_mem_equatorialArc {r θ : ℝ} (hr : r ≤ Real.pi)
    (hθ : θ ∈ Set.Icc (-r) r) : complexLift (polarRay θ) ∈ equatorialArc r := by
  have bound := (abs_le.mpr hθ).trans hr
  exact ⟨θ, (equatorPhase_mem_closedBall_iff bound).mpr hθ, equatorPoint_coe_eq_complexLift θ⟩

/-- The equatorial phase ball has real representatives in the corresponding
closed interval up to a half-turn. -/
theorem equatorialArc_eq_image_complexLift {r : ℝ} (small : r ≤ Real.pi) :
    equatorialArc r = (fun t : ℝ => complexLift (polarRay t)) '' Set.Icc (-r) r := by
  ext x
  constructor
  · intro member
    obtain ⟨t, ht, rfl⟩ := eq_polar_of_equatorialArc member
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact complexLift_polarRay_mem_equatorialArc small ht

theorem equatorialArc_eq_closedMinorArc {r : ℝ} (r_pos : 0 < r) (r_small : 2 * r < Real.pi) :
    equatorialArc r = closedMinorArc
      (equatorPoint ((-r : ℝ) : EquatorPhase)) (equatorPoint (r : EquatorPhase)) := by
  have r_le : r ≤ Real.pi := by linarith
  rw [equatorPoint_coe_eq_complexLift, equatorPoint_coe_eq_complexLift]
  ext x
  constructor
  · intro h
    obtain ⟨θ, hθ, rfl⟩ := eq_polar_of_equatorialArc h
    rcases eq_or_lt_of_le hθ.1 with equal | left
    · rw [← equal]
      exact Set.mem_insert _ _
    · rcases eq_or_lt_of_le hθ.2 with equal | right
      · rw [equal]
        exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · obtain ⟨a, ha, b, hb, combination⟩ :=
          polarRay_mem_strict_positive_span (-r) r θ (by linarith) ⟨left, right⟩
        have ab : 0 < a + b := add_pos ha hb
        let t := b / (a + b)
        have ht : t ∈ Set.Ioo 0 1 := ⟨div_pos hb ab, (div_lt_one ab).mpr (by linarith)⟩
        have sum :
            (1 - t) • complexLift (polarRay (-r)) + t • complexLift (polarRay r) =
            (a + b)⁻¹ • complexLift (polarRay θ) := by
          have a_eq : 1 - t = (a + b)⁻¹ * a := by
            dsimp [t]
            field_simp [ab.ne']
            ring
          have b_eq : t = (a + b)⁻¹ * b := by dsimp [t]; ring
          rw [a_eq, b_eq, combination, map_add, map_smul, map_smul, smul_add, smul_smul, smul_smul]
        have unit : ‖complexLift (polarRay θ)‖ = 1 := by simp
        exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
          (show complexLift (polarRay θ) ∈ openMinorArc _ _ from
            ⟨t, ht, by rw [sum, NormedSpace.normalize_smul_of_pos (inv_pos.mpr ab),
              NormedSpace.normalize_eq_self_of_norm_eq_one unit]⟩))
  · intro hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact complexLift_polarRay_mem_equatorialArc r_le ⟨le_rfl, by linarith⟩
    · rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact complexLift_polarRay_mem_equatorialArc r_le ⟨by linarith, le_rfl⟩
      · obtain ⟨t, ht, rfl⟩ := hx
        let w := (1 - t) • (1 : ℂ) + t • polarRay (2 * r)
        have w_in : w ∈ planarSector (2 * r) :=
          ⟨1 - t, by linarith [ht.2], t, ht.1.le, by simp [w, Complex.real_smul]⟩
        have w_ne : w ≠ 0 := by
          have imag : w.im = t * Real.sin (2 * r) := by simp [w, Complex.real_smul, Complex.mul_im]
          intro zero
          rw [zero, Complex.zero_im] at imag
          exact (mul_pos ht.1 (Real.sin_pos_of_pos_of_lt_pi (by linarith) r_small)).ne' imag.symm
        obtain ⟨s, s_pos, θ, hθ, w_eq⟩ :=
          exists_polar_of_mem_planarSector (2 * r) (by linarith) r_small w w_in w_ne
        have expression :
            (1 - t) • complexLift (polarRay (-r)) + t • complexLift (polarRay r) =
            s • complexLift (polarRay (θ - r)) := by
          have shift : polarRay (-r) * polarRay (2 * r) = polarRay r := by
            rw [← polarRay_add, show -r + 2 * r = r by ring]
          have coord : polarRay (-r) * w = (1 - t) • polarRay (-r) + t • polarRay r := by
            simp only [w, Complex.real_smul, mul_add, mul_one]
            have eq :
                polarRay (-r) * ((t : ℂ) * polarRay (2 * r)) =
                  (t : ℂ) * (polarRay (-r) * polarRay (2 * r)) := by ring
            rw [eq, shift]
            ring
          rw [← map_smul, ← map_smul, ← map_add, ← coord, w_eq, ← mul_assoc,
            mul_comm (polarRay (-r)) (s : ℂ), mul_assoc, ← polarRay_add, ← Complex.real_smul,
            map_smul, neg_add_eq_sub]
        rw [expression, NormedSpace.normalize_smul_of_pos s_pos,
          NormedSpace.normalize_eq_self_of_norm_eq_one (by simp)]
        exact complexLift_polarRay_mem_equatorialArc r_le
          ⟨by linarith [hθ.1], by linarith [hθ.2]⟩

theorem image_closedMinorArc (g : SpatialRotation) (u v : Space) :
    linear g '' closedMinorArc u v = closedMinorArc (linear g u) (linear g v) := by
  have map_arc : linear g '' openMinorArc u v = openMinorArc (linear g u) (linear g v) := by
    have map_point (t : ℝ) :
        linear g (NormedSpace.normalize ((1 - t) • u + t • v)) =
          NormedSpace.normalize ((1 - t) • linear g u + t • linear g v) := by
      have mapped : (1 - t) • linear g u + t • linear g v =
          linear g ((1 - t) • u + t • v) := by simp only [map_add, map_smul]
      have mapped_norm := (isometry g).norm_map ((1 - t) • u + t • v)
      change ‖linear g ((1 - t) • u + t • v)‖ = _ at mapped_norm
      rw [NormedSpace.normalize, NormedSpace.normalize, mapped, mapped_norm, map_smul]
    ext x
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t, ht, (map_point t).symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨_, ⟨t, ht, rfl⟩, map_point t⟩
  rw [closedMinorArc, Set.image_insert_eq, Set.image_insert_eq, map_arc]
  rfl

/-- Every genuine minor arc can be used as a moving side in finite-arc
Crofton. The interval radius is half the spherical angular length. -/
theorem exists_frame_closedMinorArc {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (positive : 0 < angle u v) (small : angle u v < Real.pi) :
    ∃ frame : SpatialRotation,
      linear frame '' equatorialArc (angle u v / 2) = closedMinorArc u v := by
  obtain ⟨g, left, right⟩ := exists_centered_arc_rotation hu hv
  refine ⟨g⁻¹, ?_⟩
  have arc := equatorialArc_eq_closedMinorArc (r := angle u v / 2) (by positivity) (by linarith)
  rw [← left, ← right] at arc
  rw [arc, image_closedMinorArc, linear_inv_apply, linear_inv_apply]

end Unfoldings.SpatialRotation
