module

public import Unfoldings.Geometry.SpatialRotationSphere
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Uniform angular phase on an equator, and the rotations that change only that phase. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialRotation

open Matrix MeasureTheory
open scoped ENNReal

/-- Angular coordinate modulo one turn. -/
abbrev EquatorPhase := AddCircle (2 * Real.pi)

instance equatorPhase_period_pos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def phaseComplex (t : EquatorPhase) : ℂ := ↑(AddCircle.toCircle t)

private theorem phaseComplex_add (s t : EquatorPhase) :
    phaseComplex (s + t) = phaseComplex s * phaseComplex t := by
  simp [phaseComplex, AddCircle.toCircle_add]

theorem phaseComplex_sq (t : EquatorPhase) :
    (phaseComplex t).re * (phaseComplex t).re + (phaseComplex t).im * (phaseComplex t).im = 1 := by
  have h := Complex.sq_norm (phaseComplex t)
  simp only [phaseComplex, Circle.norm_coe, one_pow, Complex.normSq_apply] at h
  exact h.symm

private theorem continuous_phaseComplex : Continuous phaseComplex :=
  continuous_subtype_val.comp AddCircle.continuous_toCircle

/-- The equator whose normal is the third coordinate direction. -/
def equatorPoint (t : EquatorPhase) : Space :=
  WithLp.toLp 2 ![(phaseComplex t).re, (phaseComplex t).im, 0]

theorem equatorPoint_unit (t : EquatorPhase) : ‖equatorPoint t‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simpa [equatorPoint, pow_two] using phaseComplex_sq t

@[simp] theorem equatorPoint_vertical (t : EquatorPhase) : equatorPoint t 2 = 0 := rfl

theorem equatorPoint_injective : Function.Injective equatorPoint := by
  intro s t equal
  apply AddCircle.injective_toCircle (by positivity : (2 : ℝ) * Real.pi ≠ 0)
  apply Subtype.ext
  refine Complex.ext ?_ ?_
  · simpa [equatorPoint, phaseComplex] using congrArg (fun x : Space => x 0) equal
  · simpa [equatorPoint, phaseComplex] using congrArg (fun x : Space => x 1) equal

theorem continuous_equatorPoint : Continuous equatorPoint := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact Complex.continuous_re.comp continuous_phaseComplex
  · exact Complex.continuous_im.comp continuous_phaseComplex
  · exact continuous_const

/-- Recover the angle on the unit equator, extending by zero off the equator. -/
def phaseAt : Space → EquatorPhase := Function.extend equatorPoint id (fun _ => 0)

@[simp] theorem phaseAt_equatorPoint (t : EquatorPhase) : phaseAt (equatorPoint t) = t :=
  equatorPoint_injective.extend_apply _ _ _

theorem equatorPoint_phaseAt {x : Space} (unit : ‖x‖ = 1) (horizontal : x 2 = 0) :
    equatorPoint (phaseAt x) = x := by
  let z : ℂ := ⟨x 0, x 1⟩
  have hz : ‖z‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [Complex.sq_norm]
    have h := EuclideanSpace.real_norm_sq_eq x
    rw [unit, Fin.sum_univ_three, horizontal] at h
    simpa [z, Complex.normSq_apply, pow_two] using h.symm
  let u : Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩
  let t : EquatorPhase := (Complex.arg z : ℝ)
  have value : AddCircle.toCircle t = u := by
    change AddCircle.toCircle ((Complex.arg z : ℝ) : EquatorPhase) = u
    rw [AddCircle.toCircle_apply_mk, div_self (by positivity : (2 : ℝ) * Real.pi ≠ 0), one_mul]
    exact Circle.exp_arg u
  have equal : equatorPoint t = x := by
    ext i
    fin_cases i
    · simpa [equatorPoint, phaseComplex, u, z] using congrArg Complex.re (congrArg Subtype.val value)
    · simpa [equatorPoint, phaseComplex, u, z] using congrArg Complex.im (congrArg Subtype.val value)
    · exact horizontal.symm
  rw [← equal, phaseAt_equatorPoint]

theorem measurable_phaseAt : Measurable phaseAt :=
  (continuous_equatorPoint.isClosedEmbedding equatorPoint_injective).measurableEmbedding
    |>.measurable_extend measurable_id measurable_const

def phaseMatrix (t : EquatorPhase) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(phaseComplex t).re, -(phaseComplex t).im, 0;
    (phaseComplex t).im, (phaseComplex t).re, 0;
    0, 0, 1]

/-- A rotation that preserves the equator and adds the given phase. -/
def phaseRotation (t : EquatorPhase) : SpatialRotation := by
  refine ⟨phaseMatrix t, Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨?_, ?_⟩⟩
  · apply (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mpr
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [phaseMatrix, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;>
      nlinarith [phaseComplex_sq t]
  · rw [Matrix.det_fin_three]
    simp [phaseMatrix, phaseComplex_sq t, pow_two]

theorem linear_phaseRotation_equatorPoint (s t : EquatorPhase) :
    linear (phaseRotation s) (equatorPoint t) = equatorPoint (s + t) := by
  ext i
  fin_cases i <;>
    simp [linear, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      phaseRotation, phaseMatrix, equatorPoint, phaseComplex_add, Complex.mul_re, Complex.mul_im] <;>
    ring

/-- The third coordinate unit vector, fixed by every equator phase shift. -/
def equatorPole : Space := WithLp.toLp 2 ![0, 0, 1]

theorem equatorPole_unit : ‖equatorPole‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, equatorPole]

theorem inner_equatorPole (x : Space) : inner ℝ equatorPole x = x 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, equatorPole, Real.inner_apply]

@[simp] theorem linear_phaseRotation_pole (t : EquatorPhase) :
    linear (phaseRotation t) equatorPole = equatorPole := by
  ext i
  fin_cases i <;>
    simp [linear, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      phaseRotation, phaseMatrix, equatorPole]

theorem continuous_phaseRotation : Continuous phaseRotation := by
  apply Continuous.subtype_mk _ _
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp [phaseMatrix] <;>
    first | exact Complex.continuous_re.comp continuous_phaseComplex |
      exact Complex.continuous_im.comp continuous_phaseComplex |
      exact (Complex.continuous_im.comp continuous_phaseComplex).neg |
      exact continuous_const

/-- The uniform angular distribution used for independent phase shifts. -/
def phaseProbability : Measure EquatorPhase :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • (volume : Measure EquatorPhase)

instance : IsProbabilityMeasure phaseProbability := by
  constructor
  rw [phaseProbability, Measure.smul_apply, AddCircle.measure_univ]
  change (ENNReal.ofReal (2 * Real.pi))⁻¹ * ENNReal.ofReal (2 * Real.pi) = 1
  exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

instance : phaseProbability.IsAddLeftInvariant := by
  unfold phaseProbability
  infer_instance

/-- A centered angular interval has probability proportional to its exact length. -/
theorem phaseProbability_closedBall (t : EquatorPhase) {r : ℝ} (nonneg : 0 ≤ r)
    (small : r ≤ Real.pi) :
    phaseProbability (Metric.closedBall t r) = ENNReal.ofReal (r / Real.pi) := by
  rw [phaseProbability, Measure.smul_apply, AddCircle.volume_closedBall,
    min_eq_right (by linarith)]
  change (ENNReal.ofReal (2 * Real.pi))⁻¹ * ENNReal.ofReal (2 * r) =
    ENNReal.ofReal (r / Real.pi)
  rw [← ENNReal.ofReal_inv_of_pos (by positivity : 0 < (2 : ℝ) * Real.pi),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (by positivity))]
  congr 1
  field_simp [Real.pi_ne_zero]

end Unfoldings.SpatialRotation
