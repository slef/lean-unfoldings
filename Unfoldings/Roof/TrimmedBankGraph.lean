module

public import Unfoldings.Roof.GraphWindowEdgeSides
public import Unfoldings.Roof.GraphWindowBankFan
public import Unfoldings.Roof.ProjectedBankMetric
public import Unfoldings.Geometry.TwoLinkClosureAlignment

/-! Trim an actual original bank and retain every internal boundary fan in its forward graph. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane (n + 2))

/-- Every trimmed link is parametrized in the positive direction of its original link. -/
theorem exists_trimmed_link_parameters (a b : unitInterval) (a_before : a.val < 1) (b_after : 0 < b.val)
    (i : Fin (n + 2)) :
    ∃ s t : unitInterval, s.val < t.val ∧
      (P.trimEnds a b).vertex i.castSucc = P.point i s ∧
      (P.trimEnds a b).vertex i.succ = P.point i t := by
  by_cases first : i = 0
  · subst i
    refine ⟨a, 1, a_before, ?_, ?_⟩
    · simpa only [Fin.castSucc_zero] using P.trimEnds_start a b
    · rw [P.point_one, P.trimEnds_vertex_internal a b _ (by simp) (by simp)]
  by_cases last : i = Fin.last (n + 1)
  · subst i
    refine ⟨0, b, b_after, ?_, ?_⟩
    · rw [P.point_zero, P.trimEnds_vertex_internal a b _ (by simp) (by simp)]
    · simpa only [Fin.succ_last] using P.trimEnds_last a b
  have lo : 0 < i.val := Nat.pos_of_ne_zero (fun eq => first (Fin.ext eq))
  have hi : i.val < n + 1 := by
    have not_max : i.val ≠ n + 1 := fun eq => last (Fin.ext eq)
    have limit := i.isLt
    omega
  refine ⟨0, 1, zero_lt_one, ?_, ?_⟩
  · rw [P.point_zero, P.trimEnds_vertex_internal a b _ lo (by exact i.isLt)]
  · rw [P.point_one, P.trimEnds_vertex_internal a b _
      (show 0 < i.val + 1 by omega) (show i.val + 1 < n + 2 by omega)]

end Unfoldings.PolygonalChain

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

theorem boundaryTurn_face {retain : Set C.Seam} (p : C.BoundaryEnd retain) :
    (C.boundaryTurn retain p).val.1.1 = p.val.1.1 := by
  calc
    _ = (C.germFarCorner p.val).1 := congrArg Prod.fst (C.boundaryTurn_corner p)
    _ = _ := rfl

theorem mateGerm_boundaryTurn_face {retain : Set C.Seam} (p : C.BoundaryEnd retain)
    (internal : ¬ C.IsBoundaryEdge Set.univ (C.germEdge p.val)) :
    (C.mateGerm Set.univ (C.boundaryTurn retain p).val).1.1 = (C.mateGerm Set.univ p.val).1.1 := by
  obtain ⟨q, crossing⟩ := (C.exists_germCrosses_iff Set.univ p.val).mpr internal
  obtain ⟨s, retained, side, flag, first, last⟩ := crossing
  have turn : (C.boundaryTurn retain p).val = C.germOfEndpoint (C.seamSide s side) (!flag) := by
    change C.germOfEndpoint (C.germEdge p.val) (!p.val.2) = _
    rw [first, C.germEdge_germOfEndpoint, C.germOfEndpoint_side]
  have across : C.GermCrosses Set.univ (C.boundaryTurn retain p).val
      (C.germOfEndpoint (C.seamSide s (!side)) (C.acrossEndpoint s side (!flag))) :=
    ⟨s, retained, side, !flag, turn, rfl⟩
  rw [C.mateGerm_of_crossing across,
    C.mateGerm_of_crossing (show C.GermCrosses Set.univ p.val q from ⟨s, retained, side, flag, first, last⟩),
    last]
  rfl

end Unfoldings.TriangleComplex
