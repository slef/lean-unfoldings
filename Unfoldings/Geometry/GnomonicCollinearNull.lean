module

public import Unfoldings.Cap.Gnomonic
public import Unfoldings.Geometry.SegmentEquation
public import Unfoldings.Geometry.CompactCollinear
public import Unfoldings.Geometry.SolidAngleSymmetry

/-! Collinear gnomonic images have zero solid angle without a tilt bound. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open MeasureTheory

def homogenizePlaneEquation (L : Plane →ᵃ[ℝ] ℝ) : Space →L[ℝ] ℝ :=
  L.linear.toContinuousLinearMap.comp Cap.horizontalCLM + (L 0) • EuclideanSpace.proj 2

theorem homogenizePlaneEquation_northLift (L : Plane →ᵃ[ℝ] ℝ) (p : Plane) :
    homogenizePlaneEquation L (Cap.northLift p) = L p := by
  change L.linear (Cap.horizontal (Cap.northLift p)) + L 0 * Cap.northLift p 2 = L p
  rw [Cap.northLift_horizontal, Cap.northLift_height, mul_one]
  exact (congrFun L.decomp p).symm

theorem homogenizePlaneEquation_ne_zero {L : Plane →ᵃ[ℝ] ℝ} (nonzero : L ≠ 0) :
    homogenizePlaneEquation L ≠ 0 := by
  intro zero
  apply nonzero
  ext p
  have equal := congrArg (fun f : Space →L[ℝ] ℝ => f (Cap.northLift p)) zero
  change L p = 0
  simpa only [homogenizePlaneEquation_northLift, zero_apply] using equal

theorem solidAngle_gnomonic_eq_zero_of_affine_zero {S : Set Plane}
    (L : Plane →ᵃ[ℝ] ℝ) (nonzero : L ≠ 0) (vanishes : ∀ p ∈ S, L p = 0) :
    solidAngleMeasure (Cap.gnomonicNormal '' S) = 0 := by
  apply measure_mono_null ?_ (solidAngleMeasure_ker (homogenizePlaneEquation L)
    (homogenizePlaneEquation_ne_zero nonzero))
  rintro _ ⟨p, hp, rfl⟩
  change homogenizePlaneEquation L (‖Cap.northLift p‖⁻¹ • Cap.northLift p) = 0
  rw [map_smul, homogenizePlaneEquation_northLift, vanishes p hp, smul_zero]

theorem solidAngle_gnomonic_eq_zero_of_compact_convex_collinear {S : Set Plane}
    (compact : IsCompact S) (convex : Convex ℝ S) (nonempty : S.Nonempty)
    (collinear : Collinear ℝ S) : solidAngleMeasure (Cap.gnomonicNormal '' S) = 0 := by
  obtain ⟨a, _ha, b, _hb, equal⟩ :=
    exists_segment_of_compact_convex_collinear compact convex nonempty collinear
  apply solidAngle_gnomonic_eq_zero_of_affine_zero (segmentEquation a b)
    (segmentEquation_ne_zero a b)
  intro p hp
  exact segmentEquation_eq_zero (equal ▸ hp)

theorem convex_collinear_of_empty_interior {S : Set Plane} (convex : Convex ℝ S)
    (empty : interior S = ∅) : Collinear ℝ S := by
  rcases S.eq_empty_or_nonempty with rfl | nonempty
  · exact collinear_empty ℝ Plane
  have proper : affineSpan ℝ S ≠ ⊤ := by
    intro top
    have inside := convex.interior_nonempty_iff_affineSpan_eq_top.mpr top
    simp only [empty, Set.not_nonempty_empty] at inside
  have dir_proper : (affineSpan ℝ S).direction ≠ ⊤ := by
    intro top
    exact proper ((AffineSubspace.direction_eq_top_iff_of_nonempty
      (nonempty.mono (subset_affineSpan ℝ S))).mp top)
  apply collinear_iff_finrank_le_one.mpr
  have less := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr dir_proper)
  rw [direction_affineSpan, finrank_top] at less
  have dimension : Module.finrank ℝ Plane = 2 := by simp [Plane]
  rw [dimension] at less
  omega

end Unfoldings
