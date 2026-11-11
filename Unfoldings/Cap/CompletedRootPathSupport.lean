module

public import Unfoldings.Cap.CompletedCrossingPotential
public import Unfoldings.Cap.OutwardRadialForest
public import Unfoldings.Geometry.ChainCoverWedges

/-! Completed paths carrying curvature stay on the prescribed geometric cuts and their wedges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Parent segment geometry depends only on the actual seam selection, not on a sector choice. -/
theorem selected_parent_segment_eq_seam {P : AscendingParents (C.Vertex Set.univ)}
    (S : P.EdgeSelection C.seamGraph) (e : {w : C.Vertex Set.univ // w ∉ P.roots}) :
    segment ℝ (K.projectedVertex e.val) (K.projectedVertex (P.parent e.val)) =
      (K.projectedTriangle (C.left (S.edge e)).face).edge (C.left (S.edge e)).edge := by
  rcases S.link e with first | last
  · rw [first.2, first.1]
    rfl
  · rw [last.2, last.1]
    exact segment_symm ℝ _ _

namespace RadialCutForest

variable {K} {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts)

theorem completedRootPath_vertex_mem {w : C.Vertex Set.univ}
    (member : K.projectedVertex w ∈ cuts)
    (i : Fin (R.spanningCompletion.parents.distanceToRoot w + 1)) :
    (R.completedRootPath w).vertex i ∈ cuts :=
  R.completed_ancestor_mem_cuts member ⟨i.val, rfl⟩

theorem completed_path_old_nonroot {w : C.Vertex Set.univ}
    (member : K.projectedVertex w ∈ cuts)
    (i : Fin (R.spanningCompletion.parents.distanceToRoot w)) :
    R.spanningCompletion.parents.parent^[i.val] w ∉ R.parents.roots := by
  intro root
  rcases (Set.ext_iff.mp R.roots_eq _).mp root with boundary | outside
  · have marked : R.spanningCompletion.parents.parent^[i.val] w ∈
        R.spanningCompletion.parents.roots :=
      (Set.ext_iff.mp R.spanningCompletion.roots_eq _).mpr boundary
    exact R.spanningCompletion.parents.iterate_lt_distanceToRoot_not_mem w i.isLt marked
  · exact outside (R.completedRootPath_vertex_mem member i.castSucc)

/-- Completing the unused roots does not change any edge of a curvature-carrying old path. -/
theorem completedRootPath_edge_subset {w : C.Vertex Set.univ}
    (member : K.projectedVertex w ∈ cuts)
    (i : Fin (R.spanningCompletion.parents.distanceToRoot w)) :
    segment ℝ ((R.completedRootPath w).vertex i.castSucc)
      ((R.completedRootPath w).vertex i.succ) ⊆ cuts := by
  let z := R.spanningCompletion.parents.parent^[i.val] w
  have nonroot : z ∉ R.parents.roots := R.completed_path_old_nonroot member i
  change segment ℝ (K.projectedVertex z)
    (K.projectedVertex (R.spanningCompletion.parents.parent^[i.val + 1] w)) ⊆ cuts
  rw [Function.iterate_succ_apply', R.spanningCompletion.parent_eq _ nonroot]
  exact (K.selected_parent_segment_eq_seam R.selection ⟨z, nonroot⟩).subset.trans
    (R.selected_subset ⟨z, nonroot⟩)

theorem completedRootPath_outward (outward : R.Outward) {w : C.Vertex Set.univ}
    (member : K.projectedVertex w ∈ cuts)
    (i : Fin (R.spanningCompletion.parents.distanceToRoot w)) :
    0 ≤ inner ℝ ((R.completedRootPath w).vertex i.castSucc - q)
      ((R.completedRootPath w).edge i) := by
  let z := R.spanningCompletion.parents.parent^[i.val] w
  have nonroot : z ∉ R.parents.roots := R.completed_path_old_nonroot member i
  change 0 ≤ inner ℝ (K.projectedVertex z - q)
    (K.projectedVertex (R.spanningCompletion.parents.parent^[i.val + 1] w) - K.projectedVertex z)
  rw [Function.iterate_succ_apply', R.spanningCompletion.parent_eq _ nonroot]
  exact outward z nonroot

/-- Derive the geometric path wedges from a finite labeled network covering the actual cuts.
Zero-curvature vertices outside that network still require no wedge or mesh-angle bound. -/
theorem curvedPathWedges_of_component_cover {I A : Type*} [Finite I]
    (outward : R.Outward) (first last : I → Plane) (label : I → A)
    (cover : cuts = ⋃ i, segment ℝ (first i) (last i))
    (piece_outward : ∀ i, 0 ≤ inner ℝ (first i - q) (last i - first i))
    (compatible : ∀ i j, (segment ℝ (first i) (last i) ∩
      segment ℝ (first j) (last j)).Nonempty → label i = label j)
    (component_wedge : ∀ a : A, ∃ u v : Plane,
      u ≠ 0 ∧ v ≠ 0 ∧ InnerProductGeometry.angle u v < Real.pi / 2 ∧
        ∀ i, label i = a → InDirectionWedge u v (last i - first i))
    (covered : ∀ w : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ w →
      K.projectedVertex w ∈ cuts) : R.CurvedPathWedges := by
  intro w curved
  have member := covered w curved
  obtain ⟨anchor, start⟩ := Set.mem_iUnion.mp (cover.subset member)
  obtain ⟨u, v, first_ne, last_ne, small, directions⟩ := component_wedge (label anchor)
  refine ⟨InnerProductGeometry.angle u v, small, ?_⟩
  apply (R.completedRootPath w).angleMonotone_of_labeled_segment_cover q u v first last label
    (R.completedRootPath_outward outward member) piece_outward compatible
    (fun i => (R.completedRootPath_edge_subset member i).trans cover.subset)
    anchor start directions first_ne last_ne

end RadialCutForest
end Unfoldings.ConvexCap
