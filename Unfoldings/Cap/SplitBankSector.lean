module

public import Unfoldings.Complex.StrictCopyAngles
public import Unfoldings.Cap.CurvatureBudget
public import Unfoldings.Cone.IntervalSector
public import Unfoldings.Cone.Charts
public import Unfoldings.Metric.BallIsometry

/-! Actual split cap-bank corners have intrinsic geometric sector charts below a full turn. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {retain : Set C.Seam} (w z : C.Vertex retain) (distinct : w ≠ z)
  (same : C.vertexForgetCuts (Set.subset_univ retain) z =
    C.vertexForgetCuts (Set.subset_univ retain) w)
  (internal : ¬ C.IsBoundaryVertex Set.univ (C.vertexForgetCuts (Set.subset_univ retain) w))

include K z distinct same internal in
/-- Every actual split bank fan is strictly below a full turn, even at zero-curvature vertices. -/
theorem split_bank_totalAngle_lt_full : C.totalAngle retain w < 2 * Real.pi :=
  (C.totalAngle_lt_forgetCuts_of_other_copy (Set.subset_univ retain) w z distinct same).trans_le
    (K.totalAngle_le_two_pi _ internal)

include K z distinct same internal in
/-- Construct the actual ordered retained bank fan and its intrinsic geometric sector.
The complementary width is positive and below a full turn, without an aperture certificate. -/
theorem exists_split_bank_sector_isometry :
    ∃ n, ∃ c : (C.linkSystem retain w).Chain n,
    ∃ _covers : ∀ p, c.Visited p,
    ∃ _start : C.linkMate retain w c.first = c.first,
    ∃ _finish : C.linkMate retain w (C.linkTurn retain w c.last) = C.linkTurn retain w c.last,
    ∃ E : C.TangentFan retain w ≃ᵢ PolygonalPoint (closedAngularSector (C.totalAngle retain w)),
      (E (C.tangentOrigin retain w)).val = 0 ∧
      (∀ x : (C.linkAngularFan retain w c).Surface,
        (E (C.angularToTangent retain w c x)).val = (C.linkAngularFan retain w c).develop x) ∧
      0 < 2 * Real.pi - C.totalAngle retain w ∧
      2 * Real.pi - C.totalAngle retain w < 2 * Real.pi := by
  have small := K.split_bank_totalAngle_lt_full w z distinct same internal
  have boundary := C.isBoundaryVertex_of_other_cut_copy (Set.subset_univ retain) w z distinct same
  obtain ⟨n, c, start, finish, covers⟩ := C.exists_interval_link retain w boundary
  refine ⟨n, c, covers, start, finish,
    C.intervalSectorIsometryEquiv retain w c covers start finish small,
    C.intervalSectorIsometryEquiv_origin retain w c covers start finish small,
    C.intervalSectorIsometryEquiv_angularToTangent retain w c covers start finish small,
    sub_pos.mpr small, ?_⟩
  linarith [C.totalAngle_pos retain w]

include K z distinct same internal in
/-- A whole ball in the actual cut cap has this sector metric, including its banks. -/
theorem exists_split_bank_corner_chart :
    ∃ r : ℝ, 0 < r ∧ ∃ a : PolygonalPoint (closedAngularSector (C.totalAngle retain w)),
      a.val = 0 ∧ Nonempty (Metric.eball (C.vertexPoint retain w) (ENNReal.ofReal r) ≃ᵢ
        Metric.eball a (ENNReal.ofReal r)) := by
  obtain ⟨n, c, covers, start, finish, E, at_center, _placement, _positive, _small⟩ :=
    K.exists_split_bank_sector_isometry w z distinct same internal
  let N := K.folding.tangentChart retain w
  exact ⟨N.radius, N.positive, E (C.tangentOrigin retain w), at_center,
    ⟨N.chart.symm.trans (basedEBallIsometry E (C.tangentOrigin retain w)
      (E (C.tangentOrigin retain w)) rfl (ENNReal.ofReal N.radius))⟩⟩

end Unfoldings.ConvexCap
