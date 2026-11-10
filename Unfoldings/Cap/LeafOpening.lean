module

public import Unfoldings.Cap.SingleCutStar
public import Unfoldings.Cap.SectorDevelopment
public import Unfoldings.Cap.RimAngles
public import Unfoldings.Topology.SelectedLeaves
public import Unfoldings.Development.BankOpening
public import Unfoldings.Development.SpatialLengths
public import Unfoldings.Complex.SingleLinkCutEndpoints

/-!
# Actual bank apertures at leaves of the constructed cap cut forest

A childless internal vertex has only its parent seam cut. Its complete cyclic
corner star becomes one actual cut boundary copy. Every actual development
therefore opens its two terminal banks by exactly the vertex curvature.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

theorem unique_cut_at_childless (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ M.parents.roots)
    (childless : ∀ u ∉ M.parents.roots, M.parents.parent u ≠ vertex)
    (s : C.Seam) (cut : s ∉ M.retain) (w : C.Vertex Set.univ)
    (link : C.seamGraph.IsLink s vertex w) : s = M.selection.edge ⟨vertex, nonroot⟩ := by
  change s ∉ (Set.range M.selection.edge)ᶜ at cut
  exact M.selection.edge_eq_at_childless nonroot childless
    (M.selection.graph_isLink_iff.mpr ⟨not_not.mp cut, link⟩)

/-- An actual leaf cut has one boundary copy carrying its entire original corner angle. -/
theorem exists_childless_cut_star (vertex : C.Vertex Set.univ)
    (nonroot : vertex ∉ M.parents.roots)
    (childless : ∀ u ∉ M.parents.roots, M.parents.parent u ≠ vertex) :
    ∃ w : C.Vertex M.retain, C.IsBoundaryVertex M.retain w ∧
      C.vertexForgetCuts (Set.subset_univ M.retain) w = vertex ∧
      C.totalAngle M.retain w = C.totalAngle Set.univ vertex := by
  have internal : ¬ C.IsBoundaryVertex Set.univ vertex := by
    simpa only [M.roots_eq, Set.mem_ofPred_eq] using nonroot
  let edge := M.selection.edge ⟨vertex, nonroot⟩
  obtain ⟨p, pedge⟩ := exists_linkGerm_at_seam (M.selection.link ⟨vertex, nonroot⟩)
  have preserves := K.preserves_other_link_pairs_of_single_cut M.retain edge p pedge
    (M.unique_cut_at_childless vertex nonroot childless)
  have cut : edge ∉ M.retain := by
    change edge ∉ (Set.range M.selection.edge)ᶜ
    exact not_not.mpr ⟨⟨vertex, nonroot⟩, rfl⟩
  have boundary : C.IsBoundaryEdge M.retain (C.germEdge p.val) := by
    rw [pedge, C.isBoundaryEdge_left_iff]
    exact cut
  refine ⟨C.vertexOfCorner M.retain p.val.1,
    C.isBoundaryVertex_of_boundary_germ M.retain p.val boundary, p.property, ?_⟩
  exact C.totalAngle_of_single_link_cut M.retain internal p preserves

/-- The opening is proved for actual banks of an actual development, including zero curvature. -/
theorem exists_childless_bank_opening (D : FacewiseDevelopment C M.retain)
    (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ M.parents.roots)
    (childless : ∀ u ∉ M.parents.roots, M.parents.parent u ≠ vertex)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi) :
    ∃ w : C.Vertex M.retain, ∃ n, ∃ c : (C.linkSystem M.retain w).Chain n,
      C.vertexForgetCuts (Set.subset_univ M.retain) w = vertex ∧
      C.linkMate M.retain w c.first = c.first ∧
      C.linkMate M.retain w (C.linkTurn M.retain w c.last) = C.linkTurn M.retain w c.last ∧
      (∀ p, c.Visited p) ∧
      NormedSpace.normalize (D.linkDevelopFrame c (D.germRay (C.linkTurn M.retain w c.last))) =
        polarRay (-(2 * Real.pi - C.totalAngle Set.univ vertex)) *
          NormedSpace.normalize (D.linkDevelopFrame c (D.germRay c.first)) ∧
      InnerProductGeometry.angle (D.germRay c.first)
        (D.germRay (C.linkTurn M.retain w c.last)) =
          2 * Real.pi - C.totalAngle Set.univ vertex := by
  classical
  have internal : ¬ C.IsBoundaryVertex Set.univ vertex := by
    simpa only [M.roots_eq, Set.mem_ofPred_eq] using nonroot
  obtain ⟨w, boundary, original, full_angle⟩ := M.exists_childless_cut_star vertex nonroot childless
  obtain ⟨n, c, start, finish, covers⟩ := C.exists_interval_link M.retain w boundary
  have nonnegative := sub_nonneg.mpr (K.totalAngle_le_two_pi vertex internal)
  have at_most_total : 2 * Real.pi - C.totalAngle Set.univ vertex ≤
      C.totalInteriorAngularDefect Set.univ := by
    have selected := K.sum_interiorAngularDefect_le_totalCurvature {vertex}
    simpa only [Finset.sum_singleton, TriangleComplex.interiorAngularDefect,
      ite_eq_right internal] using selected
  have angle : C.totalAngle M.retain w =
      2 * Real.pi - (2 * Real.pi - C.totalAngle Set.univ vertex) := by linarith
  exact ⟨w, n, c, original, start, finish, covers,
    D.normalized_bank_opening c covers angle,
    D.bank_aperture_eq_defect c covers nonnegative (at_most_total.trans budget) angle⟩

/-- The actual equal-length leaf banks differ by a rigid rotation of the actual vertex defect. -/
theorem exists_childless_rigid_bank_opening (D : FacewiseDevelopment C M.retain)
    (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ M.parents.roots)
    (childless : ∀ u ∉ M.parents.roots, M.parents.parent u ≠ vertex)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi) :
    ∃ w : C.Vertex M.retain, ∃ n, ∃ c : (C.linkSystem M.retain w).Chain n,
      C.vertexForgetCuts (Set.subset_univ M.retain) w = vertex ∧
      (∀ p, c.Visited p) ∧
      D.linkDevelopFrame c (D.germRay (C.linkTurn M.retain w c.last)) =
        polarRay (-(2 * Real.pi - C.totalAngle Set.univ vertex)) *
          D.linkDevelopFrame c (D.germRay c.first) ∧
      InnerProductGeometry.angle (D.germRay c.first)
        (D.germRay (C.linkTurn M.retain w c.last)) =
          2 * Real.pi - C.totalAngle Set.univ vertex := by
  have internal : ¬ C.IsBoundaryVertex Set.univ vertex := by
    simpa only [M.roots_eq, Set.mem_ofPred_eq] using nonroot
  let edge := M.selection.edge ⟨vertex, nonroot⟩
  obtain ⟨p, pedge⟩ := exists_linkGerm_at_seam (M.selection.link ⟨vertex, nonroot⟩)
  have preserves := K.preserves_other_link_pairs_of_single_cut M.retain edge p pedge
    (M.unique_cut_at_childless vertex nonroot childless)
  obtain ⟨w, n, c, original, start, finish, covers, _, aperture⟩ :=
    M.exists_childless_bank_opening D vertex nonroot childless budget
  have mates := C.terminal_germs_mate_of_single_link_cut M.retain internal p preserves
    original c start finish
  have lengths := D.germRay_norm_eq_of_original_mates K.folding c.first
    (C.linkTurn M.retain w c.last) mates
  have copy := C.unique_vertex_copy_of_single_link_cut M.retain internal p preserves w original
  have full := C.totalAngle_of_single_link_cut M.retain internal p preserves
  rw [← copy] at full
  have angle : C.totalAngle M.retain w =
      2 * Real.pi - (2 * Real.pi - C.totalAngle Set.univ vertex) := by linarith
  exact ⟨w, n, c, original, covers, D.bank_rotation_of_equal_length c covers angle lengths.symm,
    aperture⟩

end Unfoldings.ConvexCap.SectorForest
