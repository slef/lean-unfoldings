module

public import Unfoldings.Geometry.MonotoneStripSelection
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Fin.VecNotation

/-! Four strict axis tests give common cone bounds for finitely many affine face maps. -/

@[expose] public section

namespace Unfoldings

def affineAxisMargins (A : ℂ →ᵃ[ℝ] ℂ) : Fin 4 → ℝ :=
  ![(A.linear 1).re + (A.linear 1).im, (A.linear 1).re - (A.linear 1).im,
    (A.linear Complex.I).re + (A.linear Complex.I).im,
    (A.linear Complex.I).im - (A.linear Complex.I).re]

/-- Positive diagonal dominance controls both coordinate cones. Translation plays no role. -/
theorem affine_cone_coordinate_bounds (A : ℂ →ᵃ[ℝ] ℂ) (c : ℝ)
    (bounds : ∀ j, c ≤ affineAxisMargins A j) :
    MonotoneStrip.ConeCoordinateBound A c 1 ∧
      MonotoneStrip.ConeCoordinateBound A c (-1) := by
  have first_plus : c ≤ (A.linear 1).re + (A.linear 1).im := bounds 0
  have first_minus : c ≤ (A.linear 1).re - (A.linear 1).im := bounds 1
  have second_plus : c ≤ (A.linear Complex.I).re + (A.linear Complex.I).im := bounds 2
  have second_minus : c ≤ (A.linear Complex.I).im - (A.linear Complex.I).re := bounds 3
  have difference (a b : ℂ) : A b - A a =
      (b.re - a.re) • A.linear 1 + (b.im - a.im) • A.linear Complex.I := by
    have split : b - a = (b.re - a.re) • (1 : ℂ) +
        (b.im - a.im) • Complex.I := by
      apply Complex.ext <;> simp
    have linear : A.linear (b - a) = A b - A a := A.linear_apply_vsub b a
    rw [← linear, split, map_add, map_smul, map_smul]
  constructor
  · intro a b horizontal vertical
    simp only [one_mul] at vertical ⊢
    have first := mul_le_mul_of_nonneg_left first_plus (sub_nonneg.mpr horizontal)
    have last := mul_le_mul_of_nonneg_left second_plus (sub_nonneg.mpr vertical)
    have real := congrArg Complex.re (difference a b)
    have imaginary := congrArg Complex.im (difference a b)
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul] at real imaginary
    nlinarith
  · intro a b horizontal vertical
    have decreasing : b.im ≤ a.im := by linarith
    have first := mul_le_mul_of_nonneg_left first_minus (sub_nonneg.mpr horizontal)
    have last := mul_le_mul_of_nonneg_left second_minus (sub_nonneg.mpr decreasing)
    have real := congrArg Complex.re (difference a b)
    have imaginary := congrArg Complex.im (difference a b)
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul] at real imaginary
    nlinarith

/-- Finiteness supplies a common positive coefficient after all four axis tests are proved.
The coefficient may depend on the mesh; the geometric angle threshold need not. -/
theorem exists_common_affine_cone_bound {ι : Type*} [Finite ι]
    (A : ι → ℂ →ᵃ[ℝ] ℂ) (positive : ∀ i j, 0 < affineAxisMargins (A i) j) :
    ∃ c > 0, ∀ i, MonotoneStrip.ConeCoordinateBound (A i) c 1 ∧
      MonotoneStrip.ConeCoordinateBound (A i) c (-1) := by
  let value : Option (ι × Fin 4) → ℝ := fun entry =>
    entry.elim 1 (fun ij => affineAxisMargins (A ij.1) ij.2)
  have value_positive (entry : Option (ι × Fin 4)) : 0 < value entry := by
    cases entry with
    | none => exact zero_lt_one
    | some ij => exact positive ij.1 ij.2
  obtain ⟨entry, minimal⟩ := Finite.exists_min value
  exact ⟨value entry, value_positive entry, fun i =>
    affine_cone_coordinate_bounds (A i) (value entry) (fun j => minimal (some (i, j)))⟩

/-- A continuous finite affine selection with strict axis tests is injective on the whole strip. -/
theorem MonotoneStrip.injOn_of_affine_selection (S : MonotoneStrip)
    {ι : Type*} [Finite ι] (A : ι → ℂ →ᵃ[ℝ] ℂ)
    (continuous : ∀ i, Continuous (A i))
    (positive : ∀ i j, 0 < affineAxisMargins (A i) j)
    {F : ℂ → ℂ} (Fcontinuous : ContinuousOn F S.carrier)
    (selection : ∀ z ∈ S.carrier, ∃ i, F z = A i z) : Set.InjOn F S.carrier := by
  obtain ⟨c, cpositive, bounds⟩ := exists_common_affine_cone_bound A positive
  exact S.injOn_of_finite_selection (fun i => A i) continuous Fcontinuous selection cpositive
    (fun i => (bounds i).1) (fun i => (bounds i).2)

end Unfoldings
