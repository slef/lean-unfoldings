module

public import Unfoldings.Cap.VerticalProduct
public import Unfoldings.Geometry.SolidAngleSymmetry
public import Unfoldings.Geometry.EquivariantMeasure
public import Unfoldings.Geometry.AngleMeasure
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Group.AddCircle
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Complex.Isometry

/-!
# Uniform azimuth for spatial solid angle

Rotation about the vertical axis preserves solid angle. Away from the null
axis, complex argument is equivariant modulo a full turn. Haar uniqueness
therefore identifies its angular law without a surface Jacobian calculation.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

/-- Horizontal coordinates in the standard complex orthonormal frame. -/
def complexHorizontal : Space →ₗ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm.toLinearMap.comp Cap.horizontal

/-- A spatial vector split into its complex horizontal part and real height. -/
def complexVerticalProduct : Space ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ) :=
  Cap.verticalProduct.trans (LinearIsometryEquiv.withLpProdCongr 2
    Complex.orthonormalBasisOneI.repr.symm (LinearIsometryEquiv.refl ℝ ℝ))

/-- The argument is taken modulo a full turn; its value on the vertical axis is immaterial. -/
def azimuth (z : Space) : Real.Angle := (complexHorizontal z).arg

theorem azimuth_measurable : Measurable azimuth := by
  have quotient : Measurable (fun t : ℝ => (t : Real.Angle)) :=
    Real.Angle.continuous_coe.measurable
  exact quotient.comp (Complex.measurable_arg.comp
    complexHorizontal.continuous_of_finiteDimensional.measurable)

/-- Orthogonal rotation about the original vertical axis. -/
def azimuthRotation (θ : Real.Angle) : Space ≃ₗᵢ[ℝ] Space :=
  (complexVerticalProduct.trans (LinearIsometryEquiv.withLpProdCongr 2
    (rotation θ.toCircle) (LinearIsometryEquiv.refl ℝ ℝ))).trans complexVerticalProduct.symm

theorem complexHorizontal_azimuthRotation (θ : Real.Angle) (z : Space) :
    complexHorizontal (azimuthRotation θ z) = (θ.toCircle : ℂ) * complexHorizontal z := by
  have coordinates : complexVerticalProduct (azimuthRotation θ z) =
      (LinearIsometryEquiv.withLpProdCongr 2 (rotation θ.toCircle)
        (LinearIsometryEquiv.refl ℝ ℝ)) (complexVerticalProduct z) := by
    simp only [azimuthRotation, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.apply_symm_apply]
  have first := congrArg (fun p : WithLp 2 (ℂ × ℝ) => p.ofLp.1) coordinates
  exact first

/-- The exceptional vertical axis has zero solid angle. -/
theorem solidAngleMeasure_complexHorizontal_zero :
    solidAngleMeasure {z | complexHorizontal z = 0} = 0 := by
  let coordinate : Space →ₗ[ℝ] ℝ :=
    { toFun z := z 0
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let f : Space →L[ℝ] ℝ := coordinate.toContinuousLinearMap
  have nonzero : f ≠ 0 := by
    intro equal
    have value := congrArg (fun g : Space →L[ℝ] ℝ => g (WithLp.toLp 2 ![1, 0, 0])) equal
    change (1 : ℝ) = 0 at value
    norm_num at value
  apply measure_mono_null ?_ (solidAngleMeasure_ker f nonzero)
  intro z present
  have real := congrArg Complex.re present
  change (Complex.orthonormalBasisOneI.repr.symm (Cap.horizontal z)).re = 0 at real
  rw [Complex.orthonormalBasisOneI_repr_symm_apply] at real
  change z 0 = 0
  simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
    Cap.horizontal_apply, Fin.castSucc_zero] using real

/-- Rotation adds the prescribed angle except on the null vertical axis. -/
theorem azimuth_ae_equivariant (θ : Real.Angle) :
    ∀ᵐ z ∂solidAngleMeasure, azimuth (azimuthRotation θ z) = θ + azimuth z := by
  have nonzero : ∀ᵐ z ∂solidAngleMeasure, complexHorizontal z ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using solidAngleMeasure_complexHorizontal_zero
  filter_upwards [nonzero] with z hz
  change ((complexHorizontal (azimuthRotation θ z)).arg : Real.Angle) =
    θ + (complexHorizontal z).arg
  rw [complexHorizontal_azimuthRotation,
    Complex.arg_mul_coe_angle (Circle.coe_ne_zero _) hz, Real.Angle.arg_toCircle]

/-- The angular distribution of horizontal direction under spatial solid angle. -/
def azimuthMeasure : Measure Real.Angle := solidAngleMeasure.map azimuth

instance : IsFiniteMeasure azimuthMeasure := by
  unfold azimuthMeasure
  infer_instance

instance : azimuthMeasure.IsAddLeftInvariant :=
  isAddLeftInvariant_map_of_ae_equivariant solidAngleMeasure azimuth azimuth_measurable
    (fun θ => azimuthRotation θ) (fun θ => solidAngleMeasure_preserving (azimuthRotation θ))
    azimuth_ae_equivariant

theorem azimuthMeasure_univ : azimuthMeasure Set.univ = ENNReal.ofReal (4 * Real.pi) := by
  rw [azimuthMeasure, Measure.map_apply azimuth_measurable MeasurableSet.univ,
    Set.preimage_univ, solidAngleMeasure_univ]

/-- Every azimuth interval has twice its angular length as spatial solid angle. -/
theorem azimuthMeasure_eq_two_volume : azimuthMeasure = (2 : ℝ≥0) • volume := by
  let c : ℝ≥0 := addHaarScalarFactor azimuthMeasure (volume : Measure Real.Angle)
  have law : azimuthMeasure = c • (volume : Measure Real.Angle) :=
    isAddLeftInvariant_eq_smul azimuthMeasure volume
  have total := congrArg (fun μ : Measure Real.Angle => μ Set.univ) law
  have circle : volume (Set.univ : Set Real.Angle) = ENNReal.ofReal (2 * Real.pi) :=
    Real.Angle.volume_univ
  rw [azimuthMeasure_univ, Measure.smul_apply, circle] at total
  have real := congrArg ENNReal.toReal total
  simp only [ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * Real.pi),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi)] at real
  have scalar : (c : ℝ) = 2 := by nlinarith [Real.pi_pos]
  have scalar_nn : c = 2 := NNReal.eq scalar
  simpa only [scalar_nn] using law

end Unfoldings
