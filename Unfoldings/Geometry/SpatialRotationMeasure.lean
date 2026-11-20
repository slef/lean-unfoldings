module

public import Unfoldings.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Group.LIntegral

/-! The compact group of spatial rotations with its normalized invariant measure. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Matrix MeasureTheory MeasureTheory.Measure
open scoped BigOperators ENNReal

/-- Orientation-preserving orthogonal transformations of three-dimensional space. -/
abbrev SpatialRotation := Matrix.specialOrthogonalGroup (Fin 3) ℝ

namespace SpatialRotation

private theorem entry_mem_Icc (g : SpatialRotation) (i j : Fin 3) :
    g.val i j ∈ Set.Icc (-1 : ℝ) 1 := by
  have orthogonal := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp g.property).1
  have diagonal := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i i) orthogonal
  have unit : (∑ k : Fin 3, g.val i k ^ 2) = 1 := by
    simpa [Matrix.mul_apply, pow_two] using diagonal
  have square : g.val i j ^ 2 ≤ 1 := by
    rw [← unit]
    exact Finset.single_le_sum (fun (k : Fin 3) _ => sq_nonneg (g.val i k)) (Finset.mem_univ j)
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp
  simpa only [sq_abs, one_pow] using square

theorem isClosed_matrix_set :
    IsClosed (Matrix.specialOrthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
  have equal :
      (Matrix.specialOrthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ)) =
        {M | M * Mᵀ = 1} ∩ {M | M.det = 1} := by
    ext M
    exact Matrix.mem_specialOrthogonalGroup_iff.trans
      (and_congr_left' (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ))
  rw [equal]
  have determinant : Continuous (fun M : Matrix (Fin 3) (Fin 3) ℝ => M.det) := by
    simp_rw [Matrix.det_apply]
    fun_prop
  exact (isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_transpose)
    continuous_const).inter (isClosed_eq determinant continuous_const)

instance : CompactSpace SpatialRotation := by
  apply isCompact_iff_compactSpace.mp
  let box : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
    Set.univ.pi (fun _ : Fin 3 => Set.univ.pi (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1))
  have compact : IsCompact box :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  exact compact.of_isClosed_subset isClosed_matrix_set
    (fun M hm _ _ _ _ => entry_mem_Icc ⟨M, hm⟩ _ _)

instance : IsTopologicalGroup SpatialRotation where
  continuous_mul :=
    (continuous_subtype_val.fst'.matrix_mul continuous_subtype_val.snd').subtype_mk _
  continuous_inv := (continuous_subtype_val.matrix_transpose).subtype_mk _

instance : SecondCountableTopology SpatialRotation := by
  let : SecondCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℝ))
  exact TopologicalSpace.Subtype.secondCountableTopology _

instance : MeasurableSpace SpatialRotation := borel SpatialRotation

instance : BorelSpace SpatialRotation := ⟨rfl⟩

/-- Normalized Haar probability on the compact rotation group. -/
def probability : Measure SpatialRotation :=
  haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

instance : IsProbabilityMeasure probability :=
  ⟨haarMeasure_self⟩

instance : probability.IsHaarMeasure := by
  unfold probability
  infer_instance

instance : probability.IsMulRightInvariant := by
  constructor
  intro g
  let ν := probability.map (· * g)
  have preserving_measurable : Measurable (fun r : SpatialRotation => r * g) :=
    (continuous_id.mul continuous_const).measurable
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff preserving_measurable.aemeasurable).mpr inferInstance
  let : ν.IsMulLeftInvariant := by dsimp only [ν]; infer_instance
  have scale := isMulInvariant_eq_smul_of_compactSpace ν probability
  have equal := congrArg (fun m : Measure SpatialRotation => m Set.univ) scale
  simp only [measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at equal
  have factor : ν.haarScalarFactor probability = 1 :=
    ENNReal.coe_injective (by simpa using equal.symm)
  exact scale.trans (by rw [factor, one_smul])

instance : probability.IsInvInvariant := by
  constructor
  let : IsProbabilityMeasure probability.inv := ⟨by simp⟩
  have scale := isMulInvariant_eq_smul_of_compactSpace probability.inv probability
  have equal := congrArg (fun m : Measure SpatialRotation => m Set.univ) scale
  simp only [measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at equal
  have factor : probability.inv.haarScalarFactor probability = 1 :=
    ENNReal.coe_injective (by simpa using equal.symm)
  exact scale.trans (by rw [factor, one_smul])

/-- Independent left and right angular shifts preserve the mean of a measurable
rotation statistic. The phase space can be a product of two uniform circles. -/
theorem lintegral_eq_average_shifts {Phase : Type*} [MeasurableSpace Phase]
    (ν : Measure Phase) [IsProbabilityMeasure ν] (left right : Phase → SpatialRotation)
    (left_measurable : Measurable left) (right_measurable : Measurable right)
    (f : SpatialRotation → ℝ≥0∞) (measurable : Measurable f) :
    (∫⁻ r, ∫⁻ t, f (left t * r * right t) ∂ν ∂probability) = ∫⁻ r, f r ∂probability := by
  have joint : Measurable (fun q : SpatialRotation × Phase => f (left q.2 * q.1 * right q.2)) :=
    measurable.comp (((left_measurable.comp measurable_snd).mul measurable_fst).mul
      (right_measurable.comp measurable_snd))
  have shifted (t : Phase) :
      (∫⁻ r, f (left t * r * right t) ∂probability) = ∫⁻ r, f r ∂probability := by
    rw [lintegral_mul_left_eq_self (μ := probability) (fun r => f (r * right t)),
      lintegral_mul_right_eq_self (μ := probability)]
  rw [lintegral_lintegral_swap joint.aemeasurable]
  simp only [shifted, lintegral_const, measure_univ, mul_one]

end SpatialRotation
end Unfoldings
