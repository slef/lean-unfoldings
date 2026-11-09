module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Tactic.Linarith

/-! Positive radial homogeneity promotes equality near an apex to equality everywhere. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_positive_lineMap_mem_ball (v z : E) {r : ℝ} (positive : 0 < r) :
    ∃ t : ℝ, 0 < t ∧ dist (AffineMap.lineMap v z t) v < r := by
  let t := r / (2 * (dist z v + 1))
  have denominator_positive : 0 < dist z v + 1 := by positivity
  have t_positive : 0 < t := div_pos positive (mul_pos (by norm_num) denominator_positive)
  have identity : t * (dist z v + 1) = r / 2 := by
    dsimp [t]
    field_simp
  have distance : dist (AffineMap.lineMap v z t) v = t * dist z v := by
    rw [dist_comm, dist_left_lineMap, Real.norm_of_nonneg t_positive.le, dist_comm v z]
  exact ⟨t, t_positive, by rw [distance]; nlinarith⟩

theorem eq_of_radial_local_eq {s u : Set E} (v : E)
    (radial_s : ∀ (z : E) (t : ℝ), 0 < t → (AffineMap.lineMap v z t ∈ s ↔ z ∈ s))
    (radial_u : ∀ (z : E) (t : ℝ), 0 < t → (AffineMap.lineMap v z t ∈ u ↔ z ∈ u))
    {r : ℝ} (positive : 0 < r)
    (near : ∀ z, dist z v < r → (z ∈ s ↔ z ∈ u)) : s = u := by
  ext z
  obtain ⟨t, t_positive, near_apex⟩ := exists_positive_lineMap_mem_ball v z positive
  exact (radial_s z t t_positive).symm.trans
    ((near _ near_apex).trans (radial_u z t t_positive))

end Unfoldings
