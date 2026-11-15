module

public import Unfoldings.Cap.FreshSourceStar
public import Unfoldings.Cap.CurvatureBudget
public import Unfoldings.Cone.IntervalSector
public import Unfoldings.Cone.ComplementaryModelCompletion

/-! Complete the actual intermediate fresh-source tangent fan by its original curvature sector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (frontier : P.ParentFrontier) (vertex : C.Vertex Set.univ) (fresh : vertex ∉ frontier.processed)

include K roots fresh in
/-- Every positive-curvature fresh source has its actual complete retained tangent fan
and an exact complementary plane completion, even if it is not a final-forest leaf.
The construction uses local intrinsic stars, with no global development of an intermediate
surface that still has unprocessed curvature. -/
theorem exists_fresh_source_completed_plane
    (positive : 0 < C.interiorAngularDefect Set.univ vertex) :
    let retain := C.processedParentRetain S (frontier.process vertex)
    ∃ w : C.Vertex retain, C.vertexForgetCuts (Set.subset_univ retain) w = vertex ∧
    C.totalAngle retain w = C.totalAngle Set.univ vertex ∧
    ∃ n, ∃ c : (C.linkSystem retain w).Chain n,
    ∃ _covers : ∀ p, c.Visited p,
    ∃ E : C.TangentFan retain w ≃ᵢ PolygonalPoint (closedAngularSector (C.totalAngle retain w)),
      (E (C.tangentOrigin retain w)).val = 0 ∧
      ∃ F : ComplementaryModelCompletion E ≃ᵢ ℂ,
        (∀ x : (C.linkAngularFan retain w c).Surface,
          F (complementaryModelOriginal E (C.angularToTangent retain w c x)) =
            (C.linkAngularFan retain w c).develop x) ∧
        (∀ y : PolygonalPoint (complementarySector (C.totalAngle retain w)),
          F (complementaryModelGap E y) = y.val) := by
  classical
  dsimp only
  let retain := C.processedParentRetain S (frontier.process vertex)
  obtain ⟨w, boundary, original, full_angle, _unique⟩ :=
    K.exists_fresh_source_cut_star S roots frontier vertex fresh
  obtain ⟨n, c, start, finish, covers⟩ := C.exists_interval_link retain w boundary
  have nonroot : vertex ∉ P.roots := fun root => fresh (frontier.roots root)
  have internal : ¬ C.IsBoundaryVertex Set.univ vertex := by
    simpa only [roots, TriangleComplex.relativeCutRoots, Set.mem_ofPred_eq] using nonroot
  have curvature : C.interiorAngularDefect Set.univ vertex =
      2 * Real.pi - C.totalAngle Set.univ vertex := by
    simp only [TriangleComplex.interiorAngularDefect, ite_eq_right internal]
  have small : C.totalAngle retain w < 2 * Real.pi := by
    rw [curvature] at positive
    rw [full_angle]
    linarith
  let E := C.intervalSectorIsometryEquiv retain w c covers start finish small
  refine ⟨w, original, full_angle, n, c, covers, E,
    C.intervalSectorIsometryEquiv_origin retain w c covers start finish small,
    complementaryModelPlaneIsometryEquiv E (C.totalAngle_pos retain w) small, ?_, ?_⟩
  · intro x
    rw [complementaryModelPlane_original]
    exact C.intervalSectorIsometryEquiv_angularToTangent retain w c covers start finish small x
  · exact complementaryModelPlane_gap E (C.totalAngle_pos retain w) small

end Unfoldings.ConvexCap
