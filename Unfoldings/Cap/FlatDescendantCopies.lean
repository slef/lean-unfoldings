module

public import Unfoldings.Cap.CompletedBranchJumpOrder
public import Unfoldings.Cap.ProjectedCoherence

/-! Flat proper descendants make every developed copy of a cut endpoint coincide. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)
  (D : FacewiseDevelopment C N.completedRetain)

/-- A leaf endpoint may acquire redundant flat completion branches. They create no developed
displacement between any of its actual vertex copies. No tilt or sector assumption is needed. -/
theorem contour_vertex_position_eq_of_flat_proper_descendants
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (flat : ∀ v : C.Vertex Set.univ, N.spanningCompletion.parents.Ancestor v e.val →
      v ≠ e.val → N.completedSubtreeCurvature v = 0)
    (target : Fin (N.completedContour.length + 1))
    (vertex : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = e.val) :
    D.boundaryPosition (N.completedContour.cycle.point target) = N.parentEntrancePoint D e 1 := by
  classical
  rw [N.parentEntrancePoint_child_index D]
  by_cases same : finRotate (N.completedContour.length + 1) (N.parentBankOpening D e).enter = target
  · rw [same]
  · obtain ⟨E, first, last⟩ :=
      (N.parentBankOpening D e).exists_entrance_excursion target vertex same
    have displacement := E.displacement D
    have zero : ∀ v : {w : C.Vertex Set.univ // w ∉ N.spanningCompletion.parents.roots},
        (if E.region (N.parentBankOpening D v).enter then
          N.parentExitVector D v - N.parentEntryVector D v else 0) = 0 := by
      intro v
      by_cases selected : E.region (N.parentBankOpening D v).enter
      · rw [ite_eq_left selected]
        have different : v.val ≠ e.val := by
          intro equal
          have same : v = e := Subtype.ext equal
          subst v
          exact (N.parentBankOpening D e).outside (E.inside _ selected)
        rw [N.completed_parent_vectors_eq_of_flat v
          (flat v.val (E.selected_descendant D v selected) different), sub_self]
      · rw [ite_eq_right selected]
    simp_rw [zero] at displacement
    rw [Finset.sum_const_zero, first, last, sub_eq_zero] at displacement
    exact displacement

theorem vertex_copy_position_eq_of_flat_proper_descendants
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (flat : ∀ v : C.Vertex Set.univ, N.spanningCompletion.parents.Ancestor v e.val →
      v ≠ e.val → N.completedSubtreeCurvature v = 0)
    (a : C.Vertex N.completedRetain)
    (original : C.vertexForgetCuts (Set.subset_univ _) a = e.val) :
    D.toPlane (C.vertexPoint N.completedRetain a) = N.parentEntrancePoint D e 1 := by
  let Q := C.boundaryCycleVertexEquiv N.completedRetain N.completedContour.cycle
    N.completedContour.closes N.completedContour.covers
  let target := Q.symm ⟨a, N.completed_all_vertices_boundary a⟩
  have at_vertex : C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target) =
      a := congrArg Subtype.val (Q.apply_symm_apply ⟨a, N.completed_all_vertices_boundary a⟩)
  have at_original : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = e.val := by
    rw [at_vertex]
    exact original
  have equal := N.contour_vertex_position_eq_of_flat_proper_descendants D e flat target at_original
  change D.toPlane (C.vertexPoint N.completedRetain
    (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target))) = _ at equal
  rwa [at_vertex] at equal

/-- Coherence includes leaf pinches even when flat completion cuts create several intrinsic
copies. It concerns equality of developed values, not equality of those intrinsic copies. -/
theorem projected_coherent_of_flat_proper_descendants
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (flat : ∀ v : C.Vertex Set.univ, N.spanningCompletion.parents.Ancestor v e.val →
      v ≠ e.val → N.completedSubtreeCurvature v = 0) :
    D.ProjectedCoherentAt K (K.projectedVertex e.val) := by
  apply D.projected_coherentAt_vertex K e.val
  intro a b first last
  exact (N.vertex_copy_position_eq_of_flat_proper_descendants D e flat a first).trans
    (N.vertex_copy_position_eq_of_flat_proper_descendants D e flat b last).symm

end Unfoldings.ConvexCap.RadialCutForest
