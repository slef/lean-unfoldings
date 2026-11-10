module

public import Unfoldings.Cone.Sector
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Rotation around a region of a finite cycle

When a selected region has one entering and one leaving edge, multiplying
its actual successive rotations cancels every internal direction. The result
relates the two actual boundary directions through the sum of the region's
unreduced turns. No simplicity of a planar drawing is assumed.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {X : Type*}

theorem polarRay_sum (s : Finset X) (angle : X → ℝ) :
    polarRay (∑ i ∈ s, angle i) = ∏ i ∈ s, polarRay (angle i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s fresh ih => rw [Finset.sum_insert fresh, Finset.prod_insert fresh, polarRay_add, ih]

variable [Fintype X]

/-- Discrete cancellation of rotations, with exactly one entrance and one exit. -/
theorem rotation_of_two_region_exits (next : Equiv.Perm X) (inside : X → Prop)
    [DecidablePred inside] (direction : X → ℂ) (nonzero : ∀ i, direction i ≠ 0)
    (turn : X → ℝ) (step : ∀ i, direction (next i) = polarRay (turn (next i)) * direction i)
    (enter leave : X) (different : enter ≠ leave)
    (enters : ¬ inside enter ∧ inside (next enter))
    (leaves : inside leave ∧ ¬ inside (next leave))
    (stable : ∀ i, i ≠ enter → i ≠ leave → (inside (next i) ↔ inside i)) :
    direction leave = polarRay (∑ i, if inside i then turn i else 0) * direction enter := by
  classical
  let numerator : ℂ := ∏ i : X, if inside i then direction i else 1
  let denominator : ℂ := ∏ i : X, if inside (next i) then direction i else 1
  let rotation := polarRay (∑ i : X, if inside i then turn i else 0)
  have numerator_ne : numerator ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    split_ifs
    · exact nonzero i
    · exact one_ne_zero
  have rotations : (∏ i : X, if inside (next i) then polarRay (turn (next i)) else 1) =
      rotation := by
    rw [Equiv.prod_comp next (fun i => if inside i then polarRay (turn i) else 1)]
    dsimp only [rotation]
    rw [polarRay_sum]
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> simp only [polarRay_zero]
  have multiplied : numerator = rotation * denominator := by
    have local_step (i : X) : (if inside (next i) then direction (next i) else 1) =
        (if inside (next i) then polarRay (turn (next i)) else 1) *
          (if inside (next i) then direction i else 1) := by
      split_ifs <;> simp only [step, mul_one]
    have product := congrArg (fun f : X → ℂ => ∏ i, f i) (funext local_step)
    simp only [Finset.prod_mul_distrib] at product
    rw [Equiv.prod_comp next (fun i => if inside i then direction i else 1), rotations] at product
    exact product
  have boundary : denominator * direction leave = numerator * direction enter := by
    have cancel (i : X) :
        (if inside (next i) then direction i else 1) * (if i = leave then direction i else 1) =
        (if inside i then direction i else 1) * (if i = enter then direction i else 1) := by
      by_cases initial : i = enter
      · subst i
        simp only [enters.1, enters.2, ite_true, ite_false, different, one_mul, mul_one]
      · by_cases terminal : i = leave
        · subst i
          simp only [leaves.1, leaves.2, ite_true, ite_false, different.symm,
            one_mul, mul_one]
        · simp only [ite_eq_right initial, ite_eq_right terminal, mul_one,
            stable i initial terminal]
    calc
      _ = ∏ i : X, ((if inside (next i) then direction i else 1) *
          (if i = leave then direction i else 1)) := by
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]
        rfl
      _ = ∏ i : X, ((if inside i then direction i else 1) *
          (if i = enter then direction i else 1)) := Finset.prod_congr rfl (fun i _ => cancel i)
      _ = _ := by
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]
        rfl
  apply mul_left_cancel₀ numerator_ne
  calc
    numerator * direction leave = (rotation * denominator) * direction leave := by rw [multiplied]
    _ = rotation * (denominator * direction leave) := mul_assoc _ _ _
    _ = rotation * (numerator * direction enter) := congrArg (rotation * ·) boundary
    _ = numerator * (rotation * direction enter) := by ring

end Unfoldings
