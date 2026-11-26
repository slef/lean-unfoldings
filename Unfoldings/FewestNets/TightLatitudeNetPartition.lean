module

public import Unfoldings.FewestNets.TightLatitudeMeanCount
public import Unfoldings.FewestNets.RevisedLatitudeNetPartition

/-! Transfer the refined count to the original-edge nonoverlapping net partition. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets RevisedLatitudeGrid Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P in
/-- Turn the refined expected count into that many actual original-edge nets. -/
theorem exists_acute_netPartition_lt_246_3_of_count {a : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6)
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ π / 2 - a)
    (interval_bound : 0.31 < a → normalizedGridCoefficient a < 246.3) :
    ∃ n : ℕ, (n : ℝ) < 246.3 / a ^ 4 ∧ C.HasNetPartition n := by
  let N := P.supportingNormals
  obtain ⟨placement, label, chosen, generic, count⟩ :=
    P.exists_revisedLatitude_component_placement_le N positive small tightSelectorCountAllowance
      (P.mean_tightLatitudeSelectedCount_le N positive small angles)
  exact ⟨_, count.trans_lt (tightSelectorCountAllowance_sum_lt positive small interval_bound),
    P.hasNetPartition_of_revisedLatitude_placement N positive small placement label chosen generic angles⟩

include P in
/-- On the analytic range the refined bound holds directly. -/
theorem exists_acute_netPartition_lt_246_3_of_le_031 {a : ℝ}
    (positive : 0 < a) (analytic : a ≤ 0.31)
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ π / 2 - a) :
    ∃ n : ℕ, (n : ℝ) < 246.3 / a ^ 4 ∧ C.HasNetPartition n :=
  P.exists_acute_netPartition_lt_246_3_of_count positive
    (by linarith only [analytic, pi_gt_three]) angles
    (fun h => (not_lt_of_ge analytic h).elim)

end Unfoldings.SpatialFolding.ConvexBoundary
