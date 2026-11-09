module

public import Unfoldings.Geometry.FrontierProjection

/-!
# A convex frontier locally contained in two supporting planes is a hinge

Radial projection from an interior point proves the converse inclusion:
near the common boundary point, each support plane contributes its whole
half-plane inside the other supporting half-space. Coincident planes are
allowed, in which case the model is a plane.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

theorem frontierProjectionFrom_eq_of_two_levels (origin x : E)
    (f g : E →L[ℝ] ℝ) (a b : ℝ) (first_below : f origin < a) (second_below : g origin < b)
    (first_level : f x = a) (second_bound : g x ≤ b)
    (projected_bound : f (frontierProjectionFrom s origin x) ≤ a)
    (projected_level : g (frontierProjectionFrom s origin x) = b) :
    frontierProjectionFrom s origin x = x := by
  let r := (gauge (-origin +ᵥ s) (x - origin))⁻¹
  have nonnegative : 0 ≤ r := inv_nonneg.mpr (gauge_nonneg _)
  change f (r • (x - origin) + origin) ≤ a at projected_bound
  change g (r • (x - origin) + origin) = b at projected_level
  rw [map_add, map_smul, map_sub, first_level] at projected_bound
  rw [map_add, map_smul, map_sub] at projected_level
  change r * (a - f origin) + f origin ≤ a at projected_bound
  change r * (g x - g origin) + g origin = b at projected_level
  have upper : r ≤ 1 := by
    by_contra larger
    have product := mul_pos (sub_pos.mpr (lt_of_not_ge larger)) (sub_pos.mpr first_below)
    nlinarith
  have lower : 1 ≤ r := by
    by_contra smaller
    have product := mul_pos (sub_pos.mpr (lt_of_not_ge smaller)) (sub_pos.mpr second_below)
    have remainder := mul_nonneg nonnegative (sub_nonneg.mpr second_bound)
    nlinarith
  have one := le_antisymm upper lower
  change r • (x - origin) + origin = x
  rw [one, one_smul, sub_add_cancel]

theorem exists_local_frontier_hinge {f g : E →L[ℝ] ℝ} {a b : ℝ}
    (convex : Convex ℝ s) (compact : IsCompact s) {origin v : E}
    (inside : origin ∈ interior s) (boundary : v ∈ frontier s)
    (first_below : f origin < a) (second_below : g origin < b)
    (supported_f : ∀ z ∈ s, f z ≤ a) (supported_g : ∀ z ∈ s, g z ≤ b)
    {r : ℝ} (positive : 0 < r)
    (cover : ∀ z ∈ frontier s, dist z v < r → f z = a ∨ g z = b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z, dist z v < δ →
      (z ∈ frontier s ↔ (f z = a ∧ g z ≤ b) ∨ (g z = b ∧ f z ≤ a)) := by
  have distinct : v ≠ origin := by intro equal; exact boundary.2 (equal ▸ inside)
  have continuous_projection := continuousAt_frontierProjectionFrom convex compact inside distinct
  obtain ⟨ε, εpos, near⟩ := Metric.continuousAt_iff.mp continuous_projection r positive
  have fixed := frontierProjectionFrom_eq_self convex inside boundary
  refine ⟨min ε r, lt_min εpos positive, ?_⟩
  intro z close
  constructor
  · intro member
    have in_body := compact.isClosed.closure_eq ▸ member.1
    rcases cover z member (close.trans_le (min_le_right _ _)) with first | second
    · exact Or.inl ⟨first, supported_g z in_body⟩
    · exact Or.inr ⟨second, supported_f z in_body⟩
  · intro levels
    have different : z ≠ origin := by
      intro equal
      rcases levels with ⟨first, _⟩ | ⟨second, _⟩
      · exact first_below.ne (equal ▸ first)
      · exact second_below.ne (equal ▸ second)
    have projected_boundary := frontierProjectionFrom_mem convex compact inside different
    have projected_member := compact.isClosed.closure_eq ▸ projected_boundary.1
    have projected_near := near (close.trans_le (min_le_left _ _))
    rw [fixed] at projected_near
    have projected_planes := cover _ projected_boundary projected_near
    have same : frontierProjectionFrom s origin z = z := by
      rcases levels with ⟨first, second⟩ | ⟨second, first⟩
      · rcases projected_planes with first_projection | second_projection
        · exact frontierProjectionFrom_eq_of_level origin z f a first_below first first_projection
        · exact frontierProjectionFrom_eq_of_two_levels origin z f g a b first_below second_below
            first second (supported_f _ projected_member) second_projection
      · rcases projected_planes with first_projection | second_projection
        · exact frontierProjectionFrom_eq_of_two_levels origin z g f b a second_below first_below
            second first (supported_g _ projected_member) first_projection
        · exact frontierProjectionFrom_eq_of_level origin z g b second_below second
            second_projection
    rwa [same] at projected_boundary

end Unfoldings
