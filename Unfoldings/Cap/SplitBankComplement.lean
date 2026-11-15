module

public import Unfoldings.Cap.SplitBankSector
public import Unfoldings.Development.BankComplementAngle

/-! Actual split cap-bank vectors compute the genuine sector complement of their retained fan. -/

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
/-- The actual bank vectors determine the complementary angle, on either side of a half-turn. -/
theorem split_bank_complementary_angle (D : FacewiseDevelopment C retain)
    {n : ℕ} (c : (C.linkSystem retain w).Chain n) (covers : ∀ p, c.Visited p) :
    positiveGapAngle
      (D.linkDevelopFrame c (D.germRay (C.linkTurn retain w c.last)))
      (D.linkDevelopFrame c (D.germRay c.first)) = 2 * Real.pi - C.totalAngle retain w :=
  D.terminal_bank_complementary_angle c covers
    (K.split_bank_totalAngle_lt_full w z distinct same internal)

include K z distinct same internal in
/-- Construct the actual split bank's ordered geometric sector model and compute its
complementary angle directly from the developed terminal vectors. -/
theorem exists_split_bank_complementary_model (D : FacewiseDevelopment C retain) :
    ∃ n, ∃ c : (C.linkSystem retain w).Chain n,
    ∃ _covers : ∀ p, c.Visited p,
    ∃ _start : C.linkMate retain w c.first = c.first,
    ∃ _finish : C.linkMate retain w (C.linkTurn retain w c.last) = C.linkTurn retain w c.last,
    ∃ E : C.TangentFan retain w ≃ᵢ PolygonalPoint (closedAngularSector (C.totalAngle retain w)),
      (E (C.tangentOrigin retain w)).val = 0 ∧
      (∀ x : (C.linkAngularFan retain w c).Surface,
        (E (C.angularToTangent retain w c x)).val = (C.linkAngularFan retain w c).develop x) ∧
      positiveGapAngle
        (D.linkDevelopFrame c (D.germRay (C.linkTurn retain w c.last)))
        (D.linkDevelopFrame c (D.germRay c.first)) = 2 * Real.pi - C.totalAngle retain w ∧
      0 < 2 * Real.pi - C.totalAngle retain w ∧
      2 * Real.pi - C.totalAngle retain w < 2 * Real.pi := by
  obtain ⟨n, c, covers, start, finish, E, center, placement, positive, small⟩ :=
    K.exists_split_bank_sector_isometry w z distinct same internal
  exact ⟨n, c, covers, start, finish, E, center, placement,
    K.split_bank_complementary_angle w z distinct same internal D c covers, positive, small⟩

end Unfoldings.ConvexCap
