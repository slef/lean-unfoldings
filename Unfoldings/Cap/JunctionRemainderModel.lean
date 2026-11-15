module

public import Unfoldings.Cap.SplitBankSector
public import Unfoldings.Cap.RimAngles
public import Unfoldings.Cone.CompletedCornerRemainder

/-! Local metric fan-surgery models keep a named original side and charge its actual curvature. -/

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
/-- Keep a named original retained side, and join its original remaining angle to the
original defect sector. The resulting metric remainder has the exact complementary width;
its angle increment is actual local curvature, bounded by the global curvature budget.
Identifying this local surgery model with a physical saved-frontier update is separate. -/
theorem exists_split_junction_remainder_model :
    let original := C.totalAngle Set.univ (C.vertexForgetCuts (Set.subset_univ retain) w)
    let untouched := C.totalAngle retain w
    ∃ F : CompletedCornerRemainder original untouched ≃ᵢ
      PolygonalPoint (closedAngularSector (2 * Real.pi - untouched)),
      (∀ x : MetricGluing.Total (fun i => PolygonalPoint
          (consecutiveSectorRegion (original - untouched) (2 * Real.pi - original) i)),
        (F (MetricGluing.point _ (MetricGluing.polygonalCoincident
          (consecutiveSectorRegion (original - untouched) (2 * Real.pi - original))) x)).val =
            x.2.val) ∧
      (2 * Real.pi - untouched) - (original - untouched) =
        C.interiorAngularDefect Set.univ (C.vertexForgetCuts (Set.subset_univ retain) w) ∧
      (2 * Real.pi - untouched) - (original - untouched) ≤
        C.totalInteriorAngularDefect Set.univ := by
  classical
  dsimp only
  let vertex := C.vertexForgetCuts (Set.subset_univ retain) w
  have internal_vertex : ¬ C.IsBoundaryVertex Set.univ vertex := internal
  have curvature : C.interiorAngularDefect Set.univ vertex =
      2 * Real.pi - C.totalAngle Set.univ vertex := by
    simp only [TriangleComplex.interiorAngularDefect, ite_eq_right internal_vertex]
  have small := K.totalAngle_le_two_pi vertex internal_vertex
  have before := C.totalAngle_lt_forgetCuts_of_other_copy (Set.subset_univ retain) w z distinct same
  refine ⟨completedCornerRemainderIsometryEquiv _ _ (C.totalAngle_pos retain w) before small,
    completedCornerRemainderIsometryEquiv_point _ _ (C.totalAngle_pos retain w) before small,
    ?_, ?_⟩
  · rw [completedCornerRemainder_angle_increment]
    exact curvature.symm
  · rw [completedCornerRemainder_angle_increment, ← curvature]
    have bound := K.sum_interiorAngularDefect_le_totalCurvature {vertex}
    simpa only [Finset.sum_singleton] using bound

end Unfoldings.ConvexCap
