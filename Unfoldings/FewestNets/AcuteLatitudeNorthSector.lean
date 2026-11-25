module

public import Unfoldings.FewestNets.AcuteLatitudePoleNeighborhood

/-! A horizontal ray bisecting the first polar sector meets no other northern sector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real Module

local notation "North" => latitudeSite 0 0

/-- The signed transverse coordinate relative to a meridian. -/
def meridianTransverse (t : ℝ) : Space →ₗ[ℝ] ℝ :=
  (-sin t) • (PiLp.projₗ 2 (fun _ : Fin 3 => ℝ) 0) +
    cos t • (PiLp.projₗ 2 (fun _ : Fin 3 => ℝ) 1)

@[simp] theorem meridianTransverse_latitudeSite (t row lon : ℝ) :
    meridianTransverse t (latitudeSite row lon) = sin row * sin (lon - t) := by
  rw [sin_sub]
  simp only [meridianTransverse, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    PiLp.projₗ_apply, latitudeSite]
  change -sin t * (sin row * cos lon) + cos t * (sin row * sin lon) = _
  ring

private theorem meridianTransverse_rotate (t u : ℝ) (p : Space) :
    meridianTransverse u p =
      cos (t - u) * meridianTransverse t p + sin (t - u) * meridianCoordinate t p := by
  have h := sin_sq_add_cos_sq t
  rw [sin_sub, cos_sub]
  simp only [meridianTransverse, meridianCoordinate, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, PiLp.projₗ_apply]
  linear_combination ((-sin u) * p 0 + cos u * p 1) * (-h)

private theorem rowLongitude_as_step (a : ℝ) (j b : ℕ) :
    rowLongitude (rowSize a j) b = b * longitudeStep a j := by
  unfold rowLongitude longitudeStep
  ring

/-- Any other northern chord triangle misses points on the bisector meridian
with strictly positive horizontal projection. -/
theorem northSectorFirst_only {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (i : Fin (rowSize a 0)) (later : 0 < i.val)
    (b : Basis (Fin 3) ℝ Space) (basis : ∀ j, b j = chordVertices a (.inl i) j)
    (p : Space) (axial : meridianTransverse (longitudeStep a 0 / 2) p = 0)
    (forward : 0 < meridianCoordinate (longitudeStep a 0 / 2) p) :
    ¬ ∀ j, 0 ≤ b.coord j p := by
  intro nonneg
  let d := longitudeStep a 0
  let t := d / 2
  let u := rowLongitude (rowSize a 0) i.val
  let v := rowLongitude (rowSize a 0) (i.val + 1)
  let row := colatitude a 0
  have d_bounds := longitudeStep_pos_lt_pi positive small (Nat.zero_le (stripCount a))
  have s_positive : 0 < sin row := sin_pos_of_pos_of_lt_pi
    (colatitude_mem positive small (Nat.zero_le _)).1
    (colatitude_mem positive small (Nat.zero_le _)).2
  have v_eq : v = u + d := by
    simp only [u, v, d, rowLongitude_as_step, Nat.cast_add, Nat.cast_one]
    ring
  have after : t < u := by
    have number : (1 : ℝ) ≤ i.val := by exact_mod_cast later
    have scaled := mul_le_mul_of_nonneg_right number d_bounds.1.le
    dsimp only [t, u, d]
    rw [rowLongitude_as_step]
    linarith only [scaled, d_bounds.1]
  have turn : v ≤ 2 * π := by
    have le_count : ((i.val + 1 : ℕ) : ℝ) ≤ rowSize a 0 := by exact_mod_cast i.isLt
    have count_nonzero : (rowSize a 0 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Nat.zero_lt_of_lt i.isLt).ne'
    dsimp only [v]
    rw [rowLongitude_as_step]
    calc
      _ ≤ (rowSize a 0 : ℝ) * longitudeStep a 0 :=
        mul_le_mul_of_nonneg_right le_count d_bounds.1.le
      _ = _ := by unfold longitudeStep; field_simp
  have expansion : b.coord 0 p • North + b.coord 1 p • latitudeSite row v +
      b.coord 2 p • latitudeSite row u = p := by
    have h := b.sum_repr p
    change (∑ j, b.coord j p • b j) = p at h
    rw [Fin.sum_univ_three, basis, basis, basis] at h
    exact h
  have sin_d : 0 < sin d := sin_pos_of_pos_of_lt_pi d_bounds.1 d_bounds.2
  have comparison (x : ℝ) :
      meridianTransverse x p =
        b.coord 1 p * (sin row * sin (v - x)) +
        b.coord 2 p * (sin row * sin (u - x)) := by
    have value := congrArg (meridianTransverse x) expansion.symm
    change meridianTransverse x p = meridianTransverse x (_ + _) at value
    simpa only [map_add, map_smul, smul_eq_mul, meridianTransverse_latitudeSite, sin_zero, zero_mul,
      mul_zero, zero_add] using value
  have position (x : ℝ) : meridianTransverse x p = sin (t - x) * meridianCoordinate t p := by
    rw [meridianTransverse_rotate t x, show meridianTransverse t p = 0 from axial, mul_zero, zero_add]
  by_cases near : u - t < π
  · have s := sin_pos_of_pos_of_lt_pi (sub_pos.mpr after) near
    have pneg : meridianTransverse u p < 0 := by
      rw [position, show t - u = -(u - t) by ring, sin_neg]
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos s) forward
    have nonneg : 0 ≤ meridianTransverse u p := by
      rw [comparison, show v - u = d by linarith only [v_eq], sub_self, sin_zero, mul_zero,
        mul_zero, add_zero]
      exact mul_nonneg (nonneg 1) (mul_pos s_positive sin_d).le
    exact pneg.not_ge nonneg
  · have lo : π < v - t := by linarith only [le_of_not_gt near, v_eq, d_bounds.1]
    have hi : v - t < 2 * π := by dsimp only [t]; linarith only [turn, d_bounds.1]
    have s : 0 < sin (t - v) := by
      have inner := sin_pos_of_pos_of_lt_pi (show 0 < 2 * π - (v - t) by linarith only [hi])
        (show 2 * π - (v - t) < π by linarith only [lo])
      rwa [show 2 * π - (v - t) = (t - v) + 2 * π by ring, sin_add_two_pi] at inner
    have ppos : 0 < meridianTransverse v p := by rw [position]; exact mul_pos s forward
    have nonpos : meridianTransverse v p ≤ 0 := by
      rw [comparison, sub_self, sin_zero, mul_zero, mul_zero, zero_add,
        show u - v = -d by linarith only [v_eq], sin_neg]
      exact mul_nonpos_of_nonneg_of_nonpos (nonneg 2) (mul_nonpos_of_nonneg_of_nonpos
        s_positive.le (neg_nonpos.mpr sin_d.le))
    exact ppos.not_ge nonpos

end Unfoldings.FewestNets.AcuteLatitudeGrid
