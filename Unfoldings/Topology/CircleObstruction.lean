module

public import Unfoldings.Topology.ContractibleLift
public import Unfoldings.Topology.QuotientRetraction
public import Mathlib.Topology.Covering.FundamentalGroupCircle
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Tactic.Linarith

/-!
# The circle obstruction to retracting a disk onto its boundary

A real lift of the circle identity would change by one on a once-around loop,
while its endpoints must agree. Covering uniqueness rules out contractibility
of the circle, and hence any retraction of a contractible disk onto its circle.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem not_contractible_addCircle : ¬ ContractibleSpace (AddCircle (1 : ℝ)) := by
  intro contractible
  let := contractible
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let quotient : ℝ → AddCircle (1 : ℝ) := (↑)
  have covering : IsCoveringMap quotient := AddCircle.isCoveringMap_coe (1 : ℝ)
  have onto : Function.Surjective quotient := by
    intro x
    exact ⟨(AddCircle.equivIco (1 : ℝ) 0 x : ℝ), AddCircle.coe_equivIco⟩
  obtain ⟨lift, lifts⟩ := exists_covering_lift_of_contractible quotient covering onto
    (ContinuousMap.id (AddCircle (1 : ℝ)))
  let loop : C(unitInterval, AddCircle (1 : ℝ)) :=
    ⟨fun t => quotient (t : ℝ), covering.continuous.comp continuous_subtype_val⟩
  let original : C(unitInterval, ℝ) := lift.comp loop
  let linear : C(unitInterval, ℝ) :=
    ⟨fun t => lift 0 + (t : ℝ), continuous_const.add continuous_subtype_val⟩
  have lift_zero : quotient (lift 0) = 0 := congrFun lifts 0
  have same_quotient : quotient ∘ original = quotient ∘ linear := by
    funext t
    change quotient (lift (quotient (t : ℝ))) = quotient (lift 0 + (t : ℝ))
    have additive : quotient (lift 0 + (t : ℝ)) = quotient (lift 0) + quotient (t : ℝ) :=
      AddCircle.coe_add (1 : ℝ) _ _
    rw [additive, lift_zero, zero_add]
    exact congrFun lifts (quotient (t : ℝ))
  have same_start : original 0 = linear 0 := by simp [original, linear, loop, quotient]
  have same := covering.eq_of_comp_eq original.continuous linear.continuous
    same_quotient 0 same_start
  have endpoint := congrFun same 1
  have period : quotient 1 = 0 := AddCircle.coe_period (1 : ℝ)
  change lift (quotient 1) = lift 0 + 1 at endpoint
  rw [period] at endpoint
  linarith

theorem not_contractible_circle : ¬ ContractibleSpace Circle := by
  intro contractible
  let := contractible
  exact not_contractible_addCircle
    (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).contractibleSpace

def circleDiskInclusion : C(Circle, Metric.closedBall (0 : ℂ) 1) :=
  ⟨fun z => ⟨z.val, Metric.sphere_subset_closedBall z.property⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem no_circle_disk_retraction (retract : C(Metric.closedBall (0 : ℂ) 1, Circle))
    (identity : ∀ z, retract (circleDiskInclusion z) = z) : False := by
  let := (convex_closedBall (0 : ℂ) 1).contractibleSpace
    ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  exact not_contractible_circle (contractible_of_retraction circleDiskInclusion retract identity)

end Unfoldings
