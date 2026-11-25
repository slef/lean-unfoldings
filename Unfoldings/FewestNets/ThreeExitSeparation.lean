module

public import Unfoldings.FewestNets.ThreeExitParents
import Mathlib.Tactic.LinearCombination

/-! Noncrossing exterior rays exclude a path from a forced east root to a forced west root. -/

@[expose] public section

namespace Unfoldings.FewestNets

open Relation

variable {V : Type*}

/-- All segments in a directed graph lie in a common planar carrier. -/
private def SegmentsIn (R : V → V → Prop) (x y : V → ℝ) (S : Set (ℝ × ℝ)) : Prop :=
  ∀ ⦃v w⦄, R v w → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    ((1 - t) * x v + t * x w, (1 - t) * y v + t * y w) ∈ S

private theorem segmentsIn_reverse {R : V → V → Prop} {x y : V → ℝ}
    {S : Set (ℝ × ℝ)} (segments : SegmentsIn R x y S) :
    SegmentsIn (fun v w => R w v) (fun v => -x v) y {p | (-p.1, p.2) ∈ S} := by
  intro v w edge t ht h1
  have member := segments edge (1 - t) (by linarith) (by linarith)
  change (-((1 - t) * -x v + t * -x w), (1 - t) * y v + t * y w) ∈ S
  convert member using 2 <;> ring

private theorem affine_crossing {a b : ℝ} (a_neg : a < 0) (b_nonneg : 0 ≤ b) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ (1 - t) * a + t * b = 0 := by
  have gap : 0 < b - a := by linarith
  refine ⟨-a / (b - a), div_pos (by linarith) gap, (div_le_iff₀ gap).mpr ?_, ?_⟩
  · linarith
  · field_simp [gap.ne']
    ring

/-- After strictly entering below a ray, any path that moves away from its
origin along the horizontal coordinate stays below it. -/
private theorem below_ray_of_path {R : V → V → Prop} {x y : V → ℝ}
    {S : Set (ℝ × ℝ)} (segments : SegmentsIn R x y S)
    (forward : ∀ ⦃v w⦄, R v w → x v < x w) {r s : V} {slope : ℝ}
    (avoids : ∀ u, x r < u → (u, y r + slope * (u - x r)) ∉ S)
    (enters : ∀ ⦃v⦄, R r v → y v < y r + slope * (x v - x r))
    (path : TransGen R r s) :
    x r < x s ∧ y s < y r + slope * (x s - x r) := by
  induction path with
  | single step => exact ⟨forward step, enters step⟩
  | @tail v w _ step ih =>
    have later := forward step
    refine ⟨ih.1.trans later, ?_⟩
    by_contra! above
    let gap (v : V) := y v - (y r + slope * (x v - x r))
    have v_neg : gap v < 0 := sub_neg.mpr ih.2
    have w_nonneg : 0 ≤ gap w := sub_nonneg.mpr above
    obtain ⟨t, t_pos, t_le, zero⟩ := affine_crossing v_neg w_nonneg
    let u := (1 - t) * x v + t * x w
    have right : x r < u := by
      dsimp [u]
      nlinarith [mul_nonneg t_pos.le (sub_nonneg.mpr later.le)]
    apply avoids u right
    have on_line : (1 - t) * y v + t * y w = y r + slope * (u - x r) := by
      dsimp [gap] at zero
      dsimp [u]
      linear_combination zero
    rw [← on_line]
    exact segments step t t_pos.le t_le

namespace ThreeExitChoices

/-- The outer rays from forced boundary vertices prevent contradictory parent
constraints. Coordinates use an east axis and the common north axis from the
slope chart. The ray slope parameters are measured against the east axis. -/
theorem no_path_of_exterior_rays (R : ThreeExitChoices V)
    (x : V → ℝ) (S : Set (ℝ × ℝ)) (eastSlope westSlope : V → ℝ)
    (segments : ∀ ⦃v w⦄, R.constraint v w → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((1 - t) * x v + t * x w, (1 - t) * R.height v + t * R.height w) ∈ S)
    (east_forward : ∀ v ∉ R.boundary, x v < x (R.eastParent v))
    (west_backward : ∀ v ∉ R.boundary, x (R.westParent v) < x v)
    (east_avoids : ∀ r, R.forcedEast r → ∀ u, x r < u →
      (u, R.height r + eastSlope r * (u - x r)) ∉ S)
    (west_avoids : ∀ s, R.forcedWest s → ∀ u, u < x s →
      (u, R.height s + westSlope s * (u - x s)) ∉ S)
    (east_enters : ∀ r, R.forcedEast r → ∀ v ∉ R.boundary, R.westParent v = r →
      R.height v < R.height r + eastSlope r * (x v - x r))
    (west_enters : ∀ s, R.forcedWest s → ∀ v ∉ R.boundary, R.eastParent v = s →
      R.height v < R.height s + westSlope s * (x v - x s))
    (separate : ∀ r s, R.forcedEast r → R.forcedWest s → ∀ u, x r < u → u < x s →
      R.height r + eastSlope r * (u - x r) ≠ R.height s + westSlope s * (u - x s)) :
    ∀ r s, R.forcedEast r → R.forcedWest s → ¬ ReflTransGen R.constraint r s := by
  intro r s east west path
  have different : r ≠ s := by
    rintro rfl
    exact (R.available r east.1).elim west.2 east.2
  have nonempty : TransGen R.constraint r s := by
    rcases reflTransGen_iff_eq_or_transGen.mp path with same | nonempty
    · exact (different same.symm).elim
    · exact nonempty
  have forward : ∀ ⦃v w⦄, R.constraint v w → x v < x w := by
    rintro v w (⟨interior, rfl⟩ | ⟨interior, rfl⟩)
    · exact east_forward v interior
    · exact west_backward w interior
  have belowEast := below_ray_of_path segments forward (east_avoids r east) (by
    intro v step
    rcases step with ⟨no, _⟩ | ⟨interior, parent⟩
    · exact (no east.1).elim
    · exact east_enters r east v interior parent) nonempty
  have reverse : TransGen (fun v w => R.constraint w v) s r := nonempty.swap _ _
  have belowWest := below_ray_of_path (segmentsIn_reverse segments)
    (fun {_ _} step => neg_lt_neg (forward step)) (slope := -westSlope s) (by
      intro u hu
      have left : -u < x s := by linarith
      have same : -westSlope s * (u - -x s) = westSlope s * (-u - x s) := by ring
      change (-u, R.height s + -westSlope s * (u - -x s)) ∉ S
      rw [same]
      exact west_avoids s west (-u) left)
    (by
      intro v step
      rcases step with ⟨interior, parent⟩ | ⟨no, _⟩
      · have below := west_enters s west v interior parent
        nlinarith only [below]
      · exact (no west.1).elim) reverse
  let diff (u : ℝ) := R.height r + eastSlope r * (u - x r) -
    (R.height s + westSlope s * (u - x s))
  have left : diff (x r) < 0 := by
    dsimp [diff]
    nlinarith [belowWest.2]
  have right : 0 < diff (x s) := by
    dsimp [diff]
    nlinarith [belowEast.2]
  obtain ⟨t, t_pos, t_le, zero⟩ := affine_crossing left right.le
  have t_lt : t < 1 := by
    by_contra! h
    have equal : t = 1 := le_antisymm t_le h
    simp [equal, right.ne'] at zero
  let u := (1 - t) * x r + t * x s
  have lo : x r < u := by
    dsimp [u]
    nlinarith [mul_pos t_pos (sub_pos.mpr belowEast.1)]
  have hi : u < x s := by
    dsimp [u]
    nlinarith [mul_pos (sub_pos.mpr t_lt) (sub_pos.mpr belowEast.1)]
  apply separate r s east west u lo hi
  dsimp [diff] at zero
  dsimp [u]
  linear_combination zero

end ThreeExitChoices

end Unfoldings.FewestNets
