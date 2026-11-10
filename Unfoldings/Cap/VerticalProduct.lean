module

public import Unfoldings.Cap.Projection
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Horizontal and vertical coordinates split space isometrically and preserve volume. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open MeasureTheory

/-- A horizontal point placed at a specified height. -/
def horizontalAtHeight (p : Plane) (t : ℝ) : Space := WithLp.toLp 2 ![p 0, p 1, t]

@[simp] theorem horizontal_horizontalAtHeight (p : Plane) (t : ℝ) :
    horizontal (horizontalAtHeight p t) = p := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem height_horizontalAtHeight (p : Plane) (t : ℝ) :
    horizontalAtHeight p t 2 = t := rfl

/-- Space split into a horizontal vector and its vertical coordinate, with the L2 product norm. -/
def verticalProduct : Space ≃ₗᵢ[ℝ] WithLp 2 (Plane × ℝ) where
  toFun z := WithLp.toLp 2 (horizontal z, z 2)
  invFun p := WithLp.toLp 2 ![p.ofLp.1 0, p.ofLp.1 1, p.ofLp.2]
  left_inv z := by ext i; fin_cases i <;> rfl
  right_inv p := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · ext i
      fin_cases i <;> rfl
    · rfl
  map_add' _ _ := by apply WithLp.ofLp_injective 2; rfl
  map_smul' _ _ := by apply WithLp.ofLp_injective 2; rfl
  norm_map' z := by
    change ‖WithLp.toLp 2 (horizontal z, z 2)‖ = ‖z‖
    have squared := horizontal_norm_sq z
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖horizontal z‖ ^ 2 + ‖z 2‖ ^ 2 = ‖z‖ ^ 2
    rw [Real.norm_eq_abs, sq_abs]
    exact squared.symm

/-- A horizontal prism expressed in the original ambient coordinates. -/
def verticalPrism (s : Set Plane) (a b : ℝ) : Set Space :=
  {z | horizontal z ∈ s ∧ z 2 ∈ Set.Icc a b}

theorem volume_verticalPrism (s : Set Plane) (measurable : MeasurableSet s) (a b : ℝ) :
    volume (verticalPrism s a b) = volume s * ENNReal.ofReal (b - a) := by
  let split : Space ≃ᵐ Plane × ℝ := verticalProduct.toMeasurableEquiv.trans
    (MeasurableEquiv.toLp 2 (Plane × ℝ)).symm
  have preserving : MeasurePreserving split :=
    verticalProduct.measurePreserving.trans (WithLp.volume_preserving_ofLp (U := Plane) (V := ℝ))
  have preimage : verticalPrism s a b = split ⁻¹' (s ×ˢ Set.Icc a b) := rfl
  rw [preimage, preserving.measure_preimage (measurable.prod measurableSet_Icc).nullMeasurableSet]
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]

end Unfoldings.Cap
