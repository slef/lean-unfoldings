module

public import Unfoldings.Roof.GnomonicArea
public import Unfoldings.Roof.NormalAreaThreshold

public import Unfoldings.Cap.ConicalArea
public import Unfoldings.Roof.Tilt

/-!
# A mesh-independent solid-angle budget for all roof normal cones

The measure is Mathlib's angular measure induced by spatial volume. Its
conical-volume representation is suitable for a direct polyhedral curvature
argument. This file supplies the uniform small budget, not the curvature identity.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open MeasureTheory
open scoped ENNReal NNReal

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- A fixed upward normal-height bound puts every slope polygon in the unit disk. -/
theorem normalPolygon_subset_unitDisk (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2)
    (v : C.Vertex Set.univ) : K.normalPolygon v ⊆ Metric.closedBall (0 : Plane) 1 := by
  have radius : Real.sqrt (1 - ((3 : ℝ) / 4) ^ 2) / ((3 : ℝ) / 4) ≤ 1 := by
    rw [div_le_one (by norm_num : (0 : ℝ) < 3 / 4)]
    have square := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 - ((3 : ℝ) / 4) ^ 2)
    nlinarith [Real.sqrt_nonneg (1 - ((3 : ℝ) / 4) ^ 2)]
  exact (K.normalPolygon_subset_disk (by norm_num : (0 : ℝ) < 3 / 4) height v).trans
    (Metric.closedBall_subset_closedBall radius)

/-- The solid angle of an actual normal polygon is controlled by its planar area. -/
theorem solidNormalPolygon_area_le (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2)
    (v : C.Vertex Set.univ) :
    solidAngleMeasure (K.sphericalNormalPolygon v) ≤ 81 * volume (K.normalPolygon v) :=
  Cap.solidAngle_gnomonic_le (K.compact_normalPolygon v) (K.normalPolygon_subset_unitDisk height v)

/-- The bound uses the already proved packing of all actual planar slope polygons. -/
theorem sum_solidNormalPolygon_area_le (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) :
    (∑ v : C.Vertex Set.univ, solidAngleMeasure (K.sphericalNormalPolygon v)) ≤
      81 * ∑ v : C.Vertex Set.univ, volume (K.normalPolygon v) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun v _ => K.solidNormalPolygon_area_le height v)

/-- A requested solid-angle budget determines a positive tilt before the cap is supplied. -/
theorem exists_tilt_solid_normal_area_lt {ε : ℝ} (positive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ K : ConvexRoof C, K.TiltBound φ →
      (∑ v : C.Vertex Set.univ, solidAngleMeasure (K.sphericalNormalPolygon v)) <
        ENNReal.ofReal ε := by
  obtain ⟨ψ, ψbounds, area⟩ := exists_tilt_normal_area_lt (C := C)
    (div_pos positive (by norm_num : (0 : ℝ) < 81))
  obtain ⟨χ, χpos, χsmall, χheight⟩ := Cap.exists_positive_tilt_of_height
    (by norm_num : (3 : ℝ) / 4 < 1)
  let φ : ℝ := min ψ χ
  have φpos : 0 < φ := lt_min ψbounds.1 χpos
  have φsmall : φ < Real.pi / 2 := (min_le_left _ _).trans_lt ψbounds.2
  refine ⟨φ, ⟨φpos, φsmall⟩, fun K tilt => ?_⟩
  have tilta := TiltBound.of_le K tilt φpos.le
    (by linarith [ψbounds.2, Real.pi_pos]) (min_le_left _ _)
  have tilth := TiltBound.of_le K tilt φpos.le
    (by linarith [χsmall, Real.pi_pos]) (min_le_right _ _)
  have height (f : Face) : (3 : ℝ) / 4 ≤ K.normal f 2 := χheight.le.trans (tilth f)
  have strict : (81 : ℝ≥0∞) * (∑ v : C.Vertex Set.univ, volume (K.normalPolygon v)) <
      81 * ENNReal.ofReal (ε / 81) := by
    exact ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) (area K tilta)
  have cancel : (81 : ℝ≥0∞) * ENNReal.ofReal (ε / 81) = ENNReal.ofReal ε := by
    have numeral : (81 : ℝ≥0∞) = ENNReal.ofReal (81 : ℝ) := by norm_num
    rw [numeral, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 81)]
    congr 1
    ring
  exact (K.sum_solidNormalPolygon_area_le height).trans_lt (strict.trans_eq cancel)

end Unfoldings.ConvexRoof
