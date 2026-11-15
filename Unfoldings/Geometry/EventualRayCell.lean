module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Choose
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Data.Set.Finite.Basic

/-! A ray in a finite convex cover eventually stays in one actual cell. -/

@[expose] public section

namespace Unfoldings

variable {V I : Type*} [AddCommGroup V] [Module ℝ V] [Finite I]

/-- A finite convex cover has an actual terminal cell for every whole ray.
No bounded truncation, polyhedral description, closedness or eventual-cell certificate is needed. -/
theorem exists_eventual_ray_cell (cells : I → Set V) (convex : ∀ i, Convex ℝ (cells i))
    (p d : V) (covered : ∀ t : ℝ, 0 ≤ t → p + t • d ∈ ⋃ i, cells i) :
    ∃ i : I, ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → p + t • d ∈ cells i := by
  classical
  let ray : ℝ →ᵃ[ℝ] V := AffineMap.lineMap p (p + d)
  have ray_apply (t : ℝ) : ray t = p + t • d := by
    rw [AffineMap.lineMap_apply_module', add_sub_cancel_left, add_comm]
  let times (i : I) : Set ℝ := ray ⁻¹' cells i
  have unbounded : ∃ i, ¬ BddAbove (times i) := by
    by_contra absent
    have each : ∀ i, ∃ b : ℝ, ∀ t ∈ times i, t ≤ b := not_exists_not.mp absent
    choose bound bounds using each
    obtain ⟨B, upper⟩ := (Set.finite_range bound).bddAbove
    let t := max B 0 + 1
    have time : 0 ≤ t := by have := le_max_right B 0; dsimp [t]; linarith
    obtain ⟨i, member⟩ := Set.mem_iUnion.mp (covered t time)
    have inside : t ∈ times i := by
      change ray t ∈ cells i
      rw [ray_apply]
      exact member
    have small : t ≤ B := (bounds i t inside).trans (upper (Set.mem_range_self i))
    have := le_max_left B 0
    dsimp [t] at small
    linarith
  obtain ⟨i, cofinal⟩ := unbounded
  obtain ⟨T, member, positive⟩ := not_bddAbove_iff.mp cofinal 0
  refine ⟨i, T, positive.le, ?_⟩
  intro t after
  obtain ⟨u, future, farther⟩ := not_bddAbove_iff.mp cofinal t
  have interval : (times i).OrdConnected :=
    convex_iff_ordConnected.mp (Convex.affine_preimage ray (convex i))
  have at_t := interval.out member future ⟨after, farther.le⟩
  change ray t ∈ cells i at at_t
  rwa [ray_apply] at at_t

end Unfoldings
