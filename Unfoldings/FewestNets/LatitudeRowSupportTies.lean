module

public import Unfoldings.FewestNets.LatitudeFiniteSites

/-! A meridional supporting plane can meet one latitude row at at most two sites. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

/-- At a nonpolar latitude and nonpolar support direction, all points at
one support level have the original longitude or its meridional reflection. -/
theorem latitudeSite_eq_or_reflected_of_inner_eq {ell row : ℝ}
    (ell_range : ell ∈ Set.Ioo 0 π) (row_range : row ∈ Set.Ioo 0 π)
    (longitude left right : ℝ)
    (same : inner ℝ (latitudeSite ell longitude) (latitudeSite row left) =
      inner ℝ (latitudeSite ell longitude) (latitudeSite row right)) :
    latitudeSite row right = latitudeSite row left ∨
      latitudeSite row right = latitudeSite row (2 * longitude - left) := by
  let x := left - longitude
  let y := right - longitude
  have left_eq : longitude + x = left := by dsimp only [x]; ring
  have right_eq : longitude + y = right := by dsimp only [y]; ring
  have first := latitudeSite_inner ell row longitude x
  have last := latitudeSite_inner ell row longitude y
  rw [left_eq] at first
  rw [right_eq] at last
  rw [first, last] at same
  have sin_prod : 0 < sin row * sin ell :=
    mul_pos (sin_pos_of_pos_of_lt_pi row_range.1 row_range.2)
      (sin_pos_of_pos_of_lt_pi ell_range.1 ell_range.2)
  have cosine : cos x = cos y := by
    have product : sin row * sin ell * (cos x - cos y) = 0 := by linarith only [same]
    exact sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_left sin_prod.ne')
  obtain ⟨q, periodic | symmetric⟩ := cos_eq_cos_iff.mp cosine
  · left
    have equivalent : right = left + q * (2 * π) := by
      dsimp only [x, y] at periodic
      linarith only [periodic]
    rw [equivalent, latitudeSite_add_int_mul_two_pi]
  · right
    have equivalent : right = (2 * longitude - left) + q * (2 * π) := by
      dsimp only [x, y] at symmetric
      linarith only [symmetric]
    rw [equivalent, latitudeSite_add_int_mul_two_pi]

/-- Three distinct sites on a nonpolar row cannot have the same support level. -/
theorem subsingleton_after_two_latitudeSupports {ell row : ℝ}
    (ell_range : ell ∈ Set.Ioo 0 π) (row_range : row ∈ Set.Ioo 0 π)
    (longitude left right other : ℝ)
    (distinct : latitudeSite row right ≠ latitudeSite row left)
    (right_level : inner ℝ (latitudeSite ell longitude) (latitudeSite row left) =
      inner ℝ (latitudeSite ell longitude) (latitudeSite row right))
    (other_level : inner ℝ (latitudeSite ell longitude) (latitudeSite row left) =
      inner ℝ (latitudeSite ell longitude) (latitudeSite row other)) :
    latitudeSite row other = latitudeSite row left ∨ latitudeSite row other = latitudeSite row right := by
  have right_reflect := (latitudeSite_eq_or_reflected_of_inner_eq ell_range row_range longitude
    left right right_level).resolve_left distinct
  rw [right_reflect]
  exact latitudeSite_eq_or_reflected_of_inner_eq ell_range row_range longitude left other other_level

end Unfoldings.FewestNets
