module

public import Unfoldings.FewestNets.LatitudePolarSupport
public import Unfoldings.FewestNets.LatitudeChordBase

/-! The pole and consecutive ring vertices form a supporting chord triangle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

/-- In a direction this close to the north pole, any other row lies
strictly below the pole's support level. -/
theorem latitude_north_support_far {a θ : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (angle : 0 < θ) (bound : θ < 0.26 * latitudeRadius a) {row : ℝ}
    (far : latitudeColatitude a 1 ≤ row) (south : row ≤ π) (longitude offset : ℝ) :
    inner ℝ (latitudeSite θ longitude) (latitudeSite row (longitude + offset)) < cos θ := by
  have r_pos := latitudeRadius_pos positive
  have step := (latitudeRowStep_bounds positive small).1
  have first : latitudeColatitude a 1 = latitudeRadius a / 2 + latitudeRowStep a := by
    simp [latitudeColatitude]
  have row_lower : 0 < row := by linarith only [far, first, step, r_pos]
  have away : θ < row - θ := by linarith only [far, first, step, bound, r_pos]
  have row_diff : row - θ ≤ π := by linarith only [south, angle]
  have theta_range : θ ≤ π := by linarith only [away, row_diff]
  have loss : 0 ≤ sin row * sin θ * (1 - cos offset) :=
    mul_nonneg (mul_nonneg (sin_nonneg_of_nonneg_of_le_pi row_lower.le south)
      (sin_nonneg_of_nonneg_of_le_pi angle.le theta_range)) (sub_nonneg.mpr (cos_le_one _))
  rw [latitudeSite_inner]
  exact (sub_le_self _ loss).trans_lt
    (cos_lt_cos_of_nonneg_of_le_pi angle.le row_diff away)

/-- Every northern cap triangle supports all sampled sites, at a strictly
positive level, and excludes all rows other than the northern ring. -/
theorem exists_latitudeNorthFan_support {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (edge : Fin (latitudeRowSize a 0)) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 0.26 * latitudeRadius a ∧ 0 < cos θ ∧
      let longitude := rowMidpoint (latitudeRowSize a 0) edge
      let n := latitudeSite θ longitude
      inner ℝ n (latitudeSite 0 0) = cos θ ∧
      inner ℝ n (latitudeRowSite a 0 edge.val) = cos θ ∧
      inner ℝ n (latitudeRowSite a 0 (edge.val + 1)) = cos θ ∧
      (∀ i ≤ latitudeStripCount a, ∀ k, inner ℝ n (latitudeRowSite a i k) ≤ cos θ) ∧
      inner ℝ n (latitudeSite π 0) < cos θ := by
  let k := latitudeRowSize a 0
  let longitude := rowMidpoint k edge
  let h := π / (k : ℝ)
  obtain ⟨θ, θ_pos, θ_small, pole, right, left⟩ :=
    latitude_north_polar_secant positive small longitude
  have θ_range : θ < π / 2 := by
    linarith only [θ_small, latitudeRadius_lt small, pi_gt_three]
  have exact₀ : rowLongitude k edge.val = longitude - h := by
    change rowLongitude k edge.val = rowMidpoint k edge - π / (k : ℝ)
    linarith only [rowMidpoint_sub_rowLongitude edge]
  have exact₁ : rowLongitude k (edge.val + 1) = longitude + h := by
    change rowLongitude k (edge.val + 1) = rowMidpoint k edge + π / (k : ℝ)
    linarith only [rowLongitude_succ_sub_rowMidpoint edge]
  have ring_row : latitudeColatitude a 0 = latitudeRadius a / 2 := by simp [latitudeColatitude]
  have base₀ : inner ℝ (latitudeSite θ longitude) (latitudeRowSite a 0 edge.val) = cos θ := by
    unfold latitudeRowSite
    rw [ring_row, exact₀]
    exact left
  have base₁ : inner ℝ (latitudeSite θ longitude) (latitudeRowSite a 0 (edge.val + 1)) = cos θ := by
    unfold latitudeRowSite
    rw [ring_row, exact₁]
    exact right
  refine ⟨θ, θ_pos, θ_small, cos_pos_of_mem_Ioo ⟨by linarith only [θ_pos, pi_pos], θ_range⟩,
    by simpa only [latitudeSite_north] using pole, base₀, base₁, ?_, ?_⟩
  · intro i valid k'
    by_cases ring_index : i = 0
    · subst i
      have h_pos : 0 ≤ h := by positivity
      have near : |longitude - rowLongitude k edge.val| ≤ h := by
        rw [exact₀, sub_sub_cancel, abs_of_nonneg h_pos]
      have row_range : latitudeColatitude a 0 ∈ Set.Icc 0 π := by
        obtain ⟨low, high⟩ := latitudeColatitude_bounds positive small valid
        have radius_half := half_pos (latitudeRadius_pos positive)
        exact ⟨low.trans' radius_half.le, by linarith only [high, radius_half]⟩
      exact (latitudeNearest_support_ge (Nat.zero_lt_of_lt edge.isLt)
        ⟨θ_pos.le, by linarith only [θ_range, pi_pos]⟩ row_range near k').trans_eq base₀
    · have later : latitudeColatitude a 1 ≤ latitudeColatitude a i := by
        have step_pos : 0 ≤ latitudeRowStep a :=
          ((mul_pos (by norm_num) (latitudeRadius_pos positive)).trans
            (latitudeRowStep_bounds positive small).1).le
        have index : (1 : ℝ) ≤ i := by exact_mod_cast (show 1 ≤ i by omega)
        simp only [latitudeColatitude, Nat.cast_one]
        exact add_le_add_right (mul_le_mul_of_nonneg_right index step_pos) _
      have high := (latitudeColatitude_bounds positive small valid).2
      have row_upper : latitudeColatitude a i ≤ π := by
        linarith only [high, latitudeRadius_pos positive]
      have strict := latitude_north_support_far positive small θ_pos θ_small later row_upper
        longitude (rowLongitude (latitudeRowSize a i) k' - longitude)
      rw [show longitude + (rowLongitude (latitudeRowSize a i) k' - longitude) =
        rowLongitude (latitudeRowSize a i) k' by ring] at strict
      exact strict.le
  · have valid : 1 ≤ latitudeStripCount a := latitudeStripCount_pos positive small
    have high := (latitudeColatitude_bounds positive small valid).2
    have far : latitudeColatitude a 1 ≤ π := by linarith only [high, latitudeRadius_pos positive]
    simpa only [add_zero, latitudeSite_south] using
      latitude_north_support_far positive small θ_pos θ_small far le_rfl longitude 0

end Unfoldings.FewestNets
