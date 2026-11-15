module

public import Unfoldings.Cap.LeafOpening
public import Unfoldings.Geometry.OpeningSourceAngle

/-! The actual leaf bank vectors give precisely the complementary source-gap sector angle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- Every actual cut copy at a childless vertex carries the entire original corner fan. -/
theorem totalAngle_at_childless_copy (vertex : C.Vertex Set.univ)
    (nonroot : vertex ∉ M.parents.roots)
    (childless : ∀ u ∉ M.parents.roots, M.parents.parent u ≠ vertex)
    (w : C.Vertex M.retain) (original : C.vertexForgetCuts (Set.subset_univ M.retain) w = vertex) :
    C.totalAngle M.retain w = C.totalAngle Set.univ vertex := by
  have internal : ¬ C.IsBoundaryVertex Set.univ vertex := by
    simpa only [M.roots_eq, Set.mem_ofPred_eq] using nonroot
  let edge := M.selection.edge ⟨vertex, nonroot⟩
  obtain ⟨p, pedge⟩ := exists_linkGerm_at_seam (M.selection.link ⟨vertex, nonroot⟩)
  have preserves := K.preserves_other_link_pairs_of_single_cut M.retain edge p pedge
    (M.unique_cut_at_childless vertex nonroot childless)
  have copy := C.unique_vertex_copy_of_single_link_cut M.retain internal p preserves w original
  have full := C.totalAngle_of_single_link_cut M.retain internal p preserves
  rwa [← copy] at full

/-- Actual named leaf banks determine a geometric source sector complementary to the actual
retained corner fan. The angle is derived from the original rigid bank directions. -/
theorem exists_childless_complementary_gap_angle (D : FacewiseDevelopment C M.retain)
    (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ M.parents.roots)
    (childless : ∀ u ∉ M.parents.roots, M.parents.parent u ≠ vertex)
    (positive : 0 < 2 * Real.pi - C.totalAngle Set.univ vertex)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi) :
    ∃ w : C.Vertex M.retain, ∃ n, ∃ c : (C.linkSystem M.retain w).Chain n,
      C.vertexForgetCuts (Set.subset_univ M.retain) w = vertex ∧
      (∀ p, c.Visited p) ∧
      initialGapAngle
        (D.linkDevelopFrame c (D.germRay (C.linkTurn M.retain w c.last)))
        (D.linkDevelopFrame c (D.germRay c.first)) =
          2 * Real.pi - C.totalAngle Set.univ vertex ∧
      C.totalAngle M.retain w + initialGapAngle
        (D.linkDevelopFrame c (D.germRay (C.linkTurn M.retain w c.last)))
        (D.linkDevelopFrame c (D.germRay c.first)) = 2 * Real.pi := by
  obtain ⟨w, n, c, original, covers, rotation, _aperture⟩ :=
    M.exists_childless_rigid_bank_opening D vertex nonroot childless budget.le
  let κ := 2 * Real.pi - C.totalAngle Set.univ vertex
  let x := D.linkDevelopFrame c (D.germRay c.first)
  let y := D.linkDevelopFrame c (D.germRay (C.linkTurn M.retain w c.last))
  have internal : ¬ C.IsBoundaryVertex Set.univ vertex := by
    simpa only [M.roots_eq, Set.mem_ofPred_eq] using nonroot
  have spent : κ ≤ C.totalInteriorAngularDefect Set.univ := by
    have bound := K.sum_interiorAngularDefect_le_totalCurvature {vertex}
    simpa only [Finset.sum_singleton, TriangleComplex.interiorAngularDefect,
      ite_eq_right internal] using bound
  have nonzero : y ≠ 0 := by
    simpa only [map_zero] using (D.linkDevelopFrame c).injective.ne
      (D.germRay_ne_zero (C.linkTurn M.retain w c.last))
  have reversed : x = complexRotation κ y := by
    change y = polarRay (-κ) * x at rotation
    rw [complexRotation_apply, rotation, ← mul_assoc, ← polarRay_add, add_neg_cancel,
      polarRay_zero, one_mul]
  have angle : initialGapAngle y x = κ := by
    rw [reversed]
    exact initialGapAngle_rotated y nonzero positive (spent.trans_lt budget)
  refine ⟨w, n, c, original, covers, angle, ?_⟩
  change C.totalAngle M.retain w + initialGapAngle y x = 2 * Real.pi
  rw [angle, M.totalAngle_at_childless_copy vertex nonroot childless w original]
  dsimp [κ]
  ring

end Unfoldings.ConvexCap.SectorForest
