module

public import Unfoldings.Geometry.SpatialPairFrame
public import Unfoldings.Geometry.LuneMeasure

/-! Spherical lune and sign-disagreement measures for arbitrary genuine spatial directions. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open MeasureTheory
open scoped ENNReal NNReal

/-- Normals positive on the first direction and negative on the second. -/
def spatialLune (u v : Space) : Set Space := {n | 0 < inner ℝ n u ∧ inner ℝ n v < 0}

theorem spatialLune_measurable (u v : Space) : MeasurableSet (spatialLune u v) := by
  have first : Continuous (fun n : Space => inner ℝ n u) := by fun_prop
  have last : Continuous (fun n : Space => inner ℝ n v) := by fun_prop
  exact ((isOpen_lt continuous_const first).inter (isOpen_lt last continuous_const)).measurableSet

/-- The spatial normal coordinates reduce actual scalar-product signs to a canonical lune. -/
theorem exists_spatialLune_frame (u v : Space) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ L : Space ≃ₗᵢ[ℝ] Space,
      spatialLune u v = L ⁻¹' canonicalLune (InnerProductGeometry.angle u v) := by
  obtain ⟨L, first, last⟩ := exists_pair_frame u v hu hv
  have upos := norm_pos_iff.mpr hu
  have vpos := norm_pos_iff.mpr hv
  refine ⟨L, ?_⟩
  ext n
  have first_inner : inner ℝ n u = ‖u‖ * (complexHorizontal (L n)).re := by
    have mapped := L.toLinearIsometry.inner_map_map n u
    change inner ℝ (L n) (L u) = inner ℝ n u at mapped
    rw [first, real_inner_smul_right, inner_complexLift] at mapped
    simpa only [Complex.one_re, Complex.one_im, mul_one, mul_zero, add_zero] using mapped.symm
  have last_inner : inner ℝ n v = ‖v‖ *
      (Real.cos (InnerProductGeometry.angle u v) * (complexHorizontal (L n)).re +
        Real.sin (InnerProductGeometry.angle u v) * (complexHorizontal (L n)).im) := by
    have mapped := L.toLinearIsometry.inner_map_map n v
    change inner ℝ (L n) (L v) = inner ℝ n v at mapped
    rw [last, real_inner_smul_right, inner_complexLift, polarRay_re, polarRay_im] at mapped
    rw [← mapped]
    ring
  change (0 < inner ℝ n u ∧ inner ℝ n v < 0) ↔ _
  rw [first_inner, last_inner, mul_pos_iff_of_pos_left upos, mul_neg_iff]
  simp only [vpos, not_lt_of_ge vpos.le, true_and, false_and, or_false]
  rfl

/-- A spatial lune has twice the actual angle between its two edge directions. -/
theorem solidAngleMeasure_spatialLune (u v : Space) (hu : u ≠ 0) (hv : v ≠ 0) :
    solidAngleMeasure (spatialLune u v) =
      ENNReal.ofReal (2 * InnerProductGeometry.angle u v) := by
  obtain ⟨L, regions⟩ := exists_spatialLune_frame u v hu hv
  rw [regions, (solidAngleMeasure_preserving L).measure_preimage
    (canonicalLune_measurable _).nullMeasurableSet]
  exact solidAngleMeasure_canonicalLune (InnerProductGeometry.angle_nonneg _ _)
    (InnerProductGeometry.angle_le_pi _ _)

/-- The directions whose scalar products with the two edge rays have different signs. -/
def spatialSignChange (u v : Space) : Set Space := {n | inner ℝ n u * inner ℝ n v < 0}

theorem spatialSignChange_eq_union (u v : Space) :
    spatialSignChange u v = spatialLune u v ∪ spatialLune v u := by
  ext n
  change inner ℝ n u * inner ℝ n v < 0 ↔
    (0 < inner ℝ n u ∧ inner ℝ n v < 0) ∨ (0 < inner ℝ n v ∧ inner ℝ n u < 0)
  rw [mul_neg_iff]
  exact or_congr Iff.rfl and_comm

theorem spatialSignChange_measurable (u v : Space) : MeasurableSet (spatialSignChange u v) := by
  rw [spatialSignChange_eq_union]
  exact (spatialLune_measurable u v).union (spatialLune_measurable v u)

/-- Averaging an edge's sign changes over the sphere measures four times its angular length. -/
theorem solidAngleMeasure_spatialSignChange (u v : Space) (hu : u ≠ 0) (hv : v ≠ 0) :
    solidAngleMeasure (spatialSignChange u v) =
      ENNReal.ofReal (4 * InnerProductGeometry.angle u v) := by
  have disjoint : Disjoint (spatialLune u v) (spatialLune v u) := by
    apply Set.disjoint_left.mpr
    intro n first last
    exact first.1.not_gt last.2
  rw [spatialSignChange_eq_union, measure_union disjoint (spatialLune_measurable v u),
    solidAngleMeasure_spatialLune u v hu hv, solidAngleMeasure_spatialLune v u hv hu,
    InnerProductGeometry.angle_comm v u]
  rw [← ENNReal.ofReal_add
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (InnerProductGeometry.angle_nonneg u v))
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (InnerProductGeometry.angle_nonneg u v))]
  congr 1
  ring

end Unfoldings
