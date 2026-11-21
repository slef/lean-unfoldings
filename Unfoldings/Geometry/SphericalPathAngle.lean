module

public import Unfoldings.Geometry.SphericalAngleChord
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-! A unit-sphere path with a chord-speed bound has the same angular-speed bound. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real InnerProductGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem angle_le_chord_speed_with_slack (f : ℝ → E) (unit : ∀ t, ‖f t‖ = 1)
    {K a b ε : ℝ} (Kpos : 0 ≤ K) (ordered : a ≤ b) (εpos : 0 < ε)
    (chord : ∀ u v, ‖f v - f u‖ ≤ K * |v - u|) :
    angle (f a) (f b) ≤ (1 + ε) * (K * (b - a)) := by
  obtain ⟨δ, δpos, small⟩ := exists_angle_le_one_add_mul_chord (E := E) εpos
  obtain ⟨n, hn⟩ := exists_nat_gt (K * (b - a) / δ)
  have npos : 0 < (n : ℝ) :=
    (div_nonneg (mul_nonneg Kpos (sub_nonneg.mpr ordered)) δpos.le).trans_lt hn
  let step := (b - a) / (n : ℝ)
  have step_nonneg : 0 ≤ step := div_nonneg (sub_nonneg.mpr ordered) npos.le
  have step_small : K * step ≤ δ := by
    have bound := (div_lt_iff₀ δpos).mp hn
    dsimp [step]
    rw [← mul_div_assoc, div_le_iff₀ npos]
    exact (bound.trans_eq (mul_comm _ _)).le
  let t (i : ℕ) := a + i * step
  have at_zero : t 0 = a := by simp [t]
  have at_end : t n = b := by
    dsimp [t, step]
    rw [mul_div_cancel₀ _ npos.ne']
    ring
  have gap (i : ℕ) : t (i + 1) - t i = step := by
    simp only [t, Nat.cast_add, Nat.cast_one]
    ring
  have local_bound (i : ℕ) :
      angle (f (t i)) (f (t (i + 1))) ≤ (1 + ε) * (K * step) := by
    have h := chord (t i) (t (i + 1))
    rw [gap, abs_of_nonneg step_nonneg] at h
    exact (small (unit _) (unit _) (h.trans step_small)).trans
      (mul_le_mul_of_nonneg_left h (by positivity))
  have chain (i : ℕ) : angle (f a) (f (t i)) ≤ i * ((1 + ε) * (K * step)) := by
    induction i with
    | zero =>
      rw [at_zero, angle_self (norm_ne_zero_iff.mp (by rw [unit]; norm_num))]
      simp
    | succ i ih =>
      rw [Nat.cast_succ, add_mul, one_mul]
      exact (angle_le_angle_add_angle (f a) (f (t i)) (f (t (i + 1)))).trans
        (add_le_add ih (local_bound i))
  have bound := chain n
  rw [at_end] at bound
  have cancel : (n : ℝ) * ((1 + ε) * (K * step)) = (1 + ε) * (K * (b - a)) := by
    dsimp [step]
    field_simp
  rwa [cancel] at bound

/-- A bound on Euclidean chord distances between unit vectors bounds the
angular distance of the endpoints with the same constant. -/
theorem angle_le_chord_speed (f : ℝ → E) (unit : ∀ t, ‖f t‖ = 1) {K : ℝ} (Kpos : 0 ≤ K)
    (chord : ∀ u v, ‖f v - f u‖ ≤ K * |v - u|) (a b : ℝ) :
    angle (f a) (f b) ≤ K * |b - a| := by
  wlog ordered : a ≤ b generalizing a b
  · rw [angle_comm, abs_sub_comm]
    exact this b a (le_of_not_ge ordered)
  rw [abs_of_nonneg (sub_nonneg.mpr ordered)]
  by_contra! bad
  let B := K * (b - a)
  let ε := (angle (f a) (f b) - B) / (2 * (1 + B))
  have Bpos : 0 ≤ B := mul_nonneg Kpos (sub_nonneg.mpr ordered)
  have εpos : 0 < ε := div_pos (sub_pos.mpr bad) (by positivity)
  have slack := angle_le_chord_speed_with_slack f unit Kpos ordered εpos chord
  have eq : ε * (2 * (1 + B)) = angle (f a) (f b) - B := by
    dsimp only [ε]
    exact div_mul_cancel₀ _ (by positivity)
  change angle (f a) (f b) ≤ (1 + ε) * B at slack
  nlinarith only [eq, slack, εpos, mul_nonneg εpos.le Bpos]

end Unfoldings
