module

public import Unfoldings.Geometry.SpatialLune

/-! Antipodal symmetry bisects solid angle across any genuine linear hemisphere. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open MeasureTheory
open scoped ENNReal NNReal

/-- A measurable antipodally symmetric region has equal mass in opposite hemispheres. -/
theorem twice_solidAngleMeasure_inter_positive (s : Set Space) (measurable : MeasurableSet s)
    (antipodal : ∀ n : Space, -n ∈ s ↔ n ∈ s) (f : Space →L[ℝ] ℝ) (nonzero : f ≠ 0) :
    2 * solidAngleMeasure (s ∩ {n | 0 < f n}) = solidAngleMeasure s := by
  let P : Set Space := s ∩ {n | 0 < f n}
  let Q : Set Space := s ∩ {n | f n < 0}
  have measurable_Q : MeasurableSet Q :=
    measurable.inter (isOpen_lt f.continuous continuous_const).measurableSet
  have preimage : (LinearIsometryEquiv.neg ℝ : Space ≃ₗᵢ[ℝ] Space) ⁻¹' Q = P := by
    ext n
    change (-n ∈ s ∧ f (-n) < 0) ↔ (n ∈ s ∧ 0 < f n)
    rw [antipodal, map_neg, neg_lt_zero]
  have equal := (solidAngleMeasure_preserving (LinearIsometryEquiv.neg ℝ)).measure_preimage
    measurable_Q.nullMeasurableSet
  rw [preimage] at equal
  have disjoint : Disjoint P Q := by
    apply Set.disjoint_left.mpr
    intro n first last
    have positive : 0 < f n := first.2
    have negative : f n < 0 := last.2
    exact positive.not_gt negative
  have union : P ∪ Q = s ∩ {n | f n ≠ 0} := by
    ext n
    change (n ∈ s ∧ 0 < f n) ∨ (n ∈ s ∧ f n < 0) ↔ (n ∈ s ∧ f n ≠ 0)
    constructor
    · rintro (⟨present, positive⟩ | ⟨present, negative⟩)
      · exact ⟨present, positive.ne'⟩
      · exact ⟨present, negative.ne⟩
    · rintro ⟨present, different⟩
      rcases lt_or_gt_of_ne different with negative | positive
      · exact Or.inr ⟨present, negative⟩
      · exact Or.inl ⟨present, positive⟩
  have null : solidAngleMeasure {n | f n ≠ 0}ᶜ = 0 := by
    simpa only [Set.compl_ofPred, not_not] using solidAngleMeasure_ker f nonzero
  have sum : solidAngleMeasure P + solidAngleMeasure Q = solidAngleMeasure s := by
    rw [← measure_union disjoint measurable_Q, union, measure_inter_conull null]
  change 2 * solidAngleMeasure P = solidAngleMeasure s
  rw [two_mul, equal]
  simpa only [equal] using sum

/-- Each genuine hemisphere has solid angle `2π`. -/
theorem solidAngleMeasure_positive (f : Space →L[ℝ] ℝ) (nonzero : f ≠ 0) :
    solidAngleMeasure {n | 0 < f n} = ENNReal.ofReal (2 * Real.pi) := by
  have twice := twice_solidAngleMeasure_inter_positive Set.univ MeasurableSet.univ
    (fun _ => Iff.rfl) f nonzero
  rw [Set.univ_inter, solidAngleMeasure_univ] at twice
  have target : (2 : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) =
      ENNReal.ofReal (4 * Real.pi) := by
    have numeral : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
    conv_lhs => arg 1; rw [numeral]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  exact (ENNReal.mul_right_inj (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)).mp
    (twice.trans target.symm)

/-- An edge's sign-disagreement angle in any hemisphere is twice its actual edge angle. -/
theorem solidAngleMeasure_spatialSignChange_inter_positive (u v : Space)
    (hu : u ≠ 0) (hv : v ≠ 0) (f : Space →L[ℝ] ℝ) (nonzero : f ≠ 0) :
    solidAngleMeasure (spatialSignChange u v ∩ {n | 0 < f n}) =
      ENNReal.ofReal (2 * InnerProductGeometry.angle u v) := by
  have antipodal (n : Space) : -n ∈ spatialSignChange u v ↔ n ∈ spatialSignChange u v := by
    change inner ℝ (-n) u * inner ℝ (-n) v < 0 ↔ inner ℝ n u * inner ℝ n v < 0
    rw [inner_neg_left, inner_neg_left, neg_mul_neg]
  have twice := twice_solidAngleMeasure_inter_positive (spatialSignChange u v)
    (spatialSignChange_measurable u v) antipodal f nonzero
  rw [solidAngleMeasure_spatialSignChange u v hu hv] at twice
  have target : (2 : ℝ≥0∞) * ENNReal.ofReal (2 * InnerProductGeometry.angle u v) =
      ENNReal.ofReal (4 * InnerProductGeometry.angle u v) := by
    have numeral : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
    conv_lhs => arg 1; rw [numeral]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  exact (ENNReal.mul_right_inj (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)).mp
    (twice.trans target.symm)

end Unfoldings
