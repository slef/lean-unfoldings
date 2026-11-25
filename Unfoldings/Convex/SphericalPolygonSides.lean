module

public import Unfoldings.Convex.PolygonSideDirections
public import Unfoldings.Geometry.GnomonicMinorArc
public import Unfoldings.Geometry.EquatorialMinorArc

/-! A bounded planar halfplane polygon gives an exact spherical halfspace system. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonSideDirections

open Cap InnerProductGeometry

variable {I : Type*} {K : Set Plane} (B : PolygonSideDirections I K)

/-- The inward plane equation of one actual spherical side, in its gnomonic frame. -/
def sphericalSideForm (i : I) : Space →ₗ[ℝ] ℝ :=
  (innerSL ℝ (B.offset i • northLift 0 - horizontalLift (B.normal i))).toLinearMap

theorem sphericalSideForm_apply (i : I) (x : Space) :
    B.sphericalSideForm i x = B.offset i * x 2 - inner ℝ (B.normal i) (horizontal x) := by
  change inner ℝ (B.offset i • northLift 0 - horizontalLift (B.normal i)) x = _
  rw [inner_sub_left, inner_smul_left, horizontal_inner (northLift 0),
    horizontal_inner (horizontalLift (B.normal i))]
  have h (p : Plane) : horizontal (horizontalLift p) = p := by
    ext j
    fin_cases j <;> rfl
  have z (p : Plane) : horizontalLift p 2 = 0 := rfl
  simp only [h, z, northLift_horizontal, northLift_height, inner_zero_left,
    zero_mul, one_mul, add_zero, zero_add, RCLike.conj_to_real]

theorem sphericalSideForm_gnomonic (i : I) (p : Plane) :
    B.sphericalSideForm i (gnomonicNormal p) =
      ‖northLift p‖⁻¹ * (B.offset i - inner ℝ (B.normal i) p) := by
  change B.sphericalSideForm i (‖northLift p‖⁻¹ • northLift p) = _
  rw [map_smul, smul_eq_mul, B.sphericalSideForm_apply,
    northLift_horizontal, northLift_height, mul_one]

theorem sphericalSideForm_ne_zero (i : I) : B.sphericalSideForm i ≠ 0 := by
  intro equal
  have value := DFunLike.congr_fun equal (gnomonicNormal B.reference)
  change B.sphericalSideForm i (gnomonicNormal B.reference) = 0 at value
  rw [B.sphericalSideForm_gnomonic] at value
  exact (mul_pos (inv_pos.mpr (norm_pos_iff.mpr (northLift_ne_zero _)))
    (sub_pos.mpr (B.strict i))).ne' value

variable [Nonempty I]

/-- The support equations force an upward direction. An equatorial or
downward direction would give an unbounded planar recession ray. -/
theorem pos_height_of_sphericalSideForms (R : ℝ) (bounded : ∀ p ∈ K, ‖p‖ ≤ R)
    {x : Space} (unit : ‖x‖ = 1) (support : ∀ i, 0 ≤ B.sphericalSideForm i x) :
    0 < x 2 := by
  by_contra! nonpos
  let d := horizontal x - x 2 • B.reference
  have bound (i : I) : inner ℝ (B.normal i) (horizontal x) ≤ B.offset i * x 2 := by
    simpa only [B.sphericalSideForm_apply, sub_nonneg] using support i
  have along (i : I) : inner ℝ (B.normal i) d ≤
      (x 2) * (B.offset i - inner ℝ (B.normal i) B.reference) := by
    dsimp only [d]
    rw [inner_sub_right, inner_smul_right]
    linarith only [bound i]
  have descends (i : I) : inner ℝ (B.normal i) d ≤ 0 :=
    (along i).trans (mul_nonpos_of_nonpos_of_nonneg nonpos (sub_nonneg.mpr (B.strict i).le))
  have nonzero : d ≠ 0 := by
    intro zero
    by_cases horizontal_direction : x 2 = 0
    · have projected : horizontal x = 0 := by
        simpa only [d, horizontal_direction, zero_smul, sub_zero] using zero
      have length := horizontal_norm_sq x
      rw [unit, projected, norm_zero, horizontal_direction] at length
      norm_num at length
    · let i : I := Classical.choice ‹Nonempty I›
      have impossible := (along i).trans_lt
        (mul_neg_of_neg_of_pos (lt_of_le_of_ne nonpos horizontal_direction)
          (sub_pos.mpr (B.strict i)))
      rw [zero, inner_zero_right] at impossible
      exact lt_irrefl _ impossible
  have ref_in : B.reference ∈ K := B.carrier_eq.symm.subset (fun i => (B.strict i).le)
  have R_nonneg : 0 ≤ R := (norm_nonneg _).trans (bounded _ ref_in)
  let t := (R + ‖B.reference‖ + 1) / ‖d‖
  have t_pos : 0 < t := div_pos (by positivity) (norm_pos_iff.mpr nonzero)
  let p := B.reference + t • d
  have p_in : p ∈ K := B.carrier_eq.symm.subset fun i => by
    change inner ℝ (B.normal i) (B.reference + t • d) ≤ B.offset i
    rw [inner_add_right, inner_smul_right]
    linarith only [B.strict i, mul_nonpos_of_nonneg_of_nonpos t_pos.le (descends i)]
  have span : ‖t • d‖ ≤ R + ‖B.reference‖ := calc
    _ = ‖p - B.reference‖ := by rw [show p - B.reference = t • d from add_sub_cancel_left _ _]
    _ ≤ ‖p‖ + ‖B.reference‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add (bounded p p_in) le_rfl
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos t_pos, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr nonzero)] at span
  linarith only [span]

/-- On the whole unit sphere, the support equations select precisely the
gnomonic polygon. This includes points below the chart's equator. -/
theorem mem_gnomonicPolygon_iff (R : ℝ) (bounded : ∀ p ∈ K, ‖p‖ ≤ R)
    {x : Space} (unit : ‖x‖ = 1) :
    x ∈ gnomonicNormal '' K ↔ ∀ i, 0 ≤ B.sphericalSideForm i x := by
  constructor
  · rintro ⟨p, hp, rfl⟩ i
    rw [B.sphericalSideForm_gnomonic]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (sub_nonneg.mpr (B.side_bound hp i))
  · intro support
    have upward := B.pos_height_of_sphericalSideForms R bounded unit support
    let p := (x 2)⁻¹ • horizontal x
    have inverse : gnomonicNormal p = x := gnomonicNormal_slope x unit upward
    refine ⟨p, B.carrier_eq.symm.subset fun i => ?_, inverse⟩
    have sides := support i
    rw [← inverse, B.sphericalSideForm_gnomonic, mul_nonneg_iff_of_pos_left
      (inv_pos.mpr (norm_pos_iff.mpr (northLift_ne_zero _))), sub_nonneg] at sides
    exact sides

end Unfoldings.PolygonSideDirections
