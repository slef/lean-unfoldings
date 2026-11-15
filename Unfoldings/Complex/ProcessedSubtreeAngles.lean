module

public import Unfoldings.Complex.ProcessedCutIncidence
public import Unfoldings.Complex.AngleCutSums
public import Unfoldings.Complex.Curvature
public import Unfoldings.Topology.ProcessedDescendantIncidence

/-! Exact original angle accounting at processed descendant copies of intermediate cuts. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (frontier : P.ParentFrontier) (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.processedParentRetain S frontier))

open Classical in
private theorem sum_processed_selectors (f : C.Vertex Set.univ → ℝ)
    (zero_roots : ∀ v ∈ P.roots, f v = 0) :
    (∑ e : C.ProcessedParentSelector frontier, f e.val.val) =
      ∑ v : C.Vertex Set.univ, if v ∈ frontier.processed then f v else 0 := by
  classical
  have outer := Finset.sum_subtype (F := C.processedParentSelector_fintype frontier)
    (p := fun e : {v : C.Vertex Set.univ // v ∉ P.roots} => e.val ∈ frontier.processed)
    (Finset.univ.filter (fun e => e.val ∈ frontier.processed)) (by simp)
    (fun e => f e.val)
  rw [← outer, Finset.sum_filter]
  have inner := Finset.sum_subtype (F := inferInstance)
    (p := fun v : C.Vertex Set.univ => v ∉ P.roots)
    (Finset.univ.filter (fun v => v ∉ P.roots)) (by simp)
    (fun v => if v ∈ frontier.processed then f v else 0)
  rw [← inner, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases root : v ∈ P.roots
  · simp only [root, not_true_eq_false, zero_roots v root, ite_self]
  · simp only [root, not_false_eq_true, ite_true]

include roots Q in
open Classical in
/-- Intermediate boundary-copy incidence counts only the processed part of the original
subtree. Unprocessed original vertices and their positive curvature remain internal. -/
theorem sum_processed_subtree_vertex_copies (vertex : C.Vertex Set.univ)
    (nonroot : vertex ∉ P.roots) (processed : vertex ∈ frontier.processed) :
    (∑ w : C.Vertex (C.processedParentRetain S frontier),
      if C.vertexForgetCuts (Set.subset_univ _) w ∈ frontier.processed ∧
        P.Ancestor (C.vertexForgetCuts (Set.subset_univ _) w) vertex then (1 : ℝ) else 0) =
      2 * (frontier.processedDescendants vertex).card - 1 := by
  classical
  let weight (v : C.Vertex Set.univ) : ℝ :=
    if v ∈ frontier.processed ∧ P.Ancestor v vertex then 1 else 0
  have zero_roots (v : C.Vertex Set.univ) (root : v ∈ P.roots) : weight v = 0 := by
    exact ite_eq_right (fun both => P.descendant_nonroot nonroot both.2 root)
  have counted := C.sum_processed_vertex_weights S frontier roots Q.cycle Q.closes Q.covers
    weight zero_roots (fun v fresh => ite_eq_right (fun both => fresh both.1))
  have reindex := C.sum_processed_selectors frontier
    (fun v => weight v + weight (P.parent v)) (by
      intro v root
      rw [zero_roots v root, P.fixed_root v root, zero_roots v root, add_zero])
  rw [reindex] at counted
  have terms (v : C.Vertex Set.univ) :
      (if v ∈ frontier.processed then weight v + weight (P.parent v) else 0) =
        (if v ∈ frontier.processed ∧ P.Ancestor v vertex then (1 : ℝ) else 0) +
          (if v ∈ frontier.processed ∧ P.Ancestor (P.parent v) vertex then (1 : ℝ) else 0) := by
    by_cases active : v ∈ frontier.processed
    · have parent_active := frontier.closed v active
      simp only [active, parent_active, true_and, ite_true, weight]
    · simp only [active, false_and, ite_false, zero_add]
  simp only [terms] at counted
  exact counted.trans (frontier.sum_processed_descendant_incidence vertex nonroot processed)

include roots Q in
open Classical in
/-- The exact aggregate original turn at the current boundary charges only processed
curvature. Fresh curved vertices are still internal and make no boundary contribution. -/
theorem sum_processed_subtree_boundary_turn (vertex : C.Vertex Set.univ)
    (nonroot : vertex ∉ P.roots) (processed : vertex ∈ frontier.processed) :
    (∑ w : C.Vertex (C.processedParentRetain S frontier),
      if C.vertexForgetCuts (Set.subset_univ _) w ∈ frontier.processed ∧
        P.Ancestor (C.vertexForgetCuts (Set.subset_univ _) w) vertex then
          C.totalAngle (C.processedParentRetain S frontier) w - Real.pi else 0) =
      Real.pi - ∑ v ∈ frontier.processedDescendants vertex, C.interiorAngularDefect Set.univ v := by
  classical
  let retain := C.processedParentRetain S frontier
  let chosen := frontier.processedDescendants vertex
  have copies := C.sum_processed_subtree_vertex_copies S frontier roots Q vertex nonroot processed
  have angles := C.sum_totalAngle_over_copies (Set.subset_univ retain) chosen
  change (∑ w : C.Vertex retain, if C.vertexForgetCuts (Set.subset_univ _) w ∈
    frontier.processedDescendants vertex then C.totalAngle retain w else 0) = _ at angles
  simp only [frontier.mem_processedDescendants, chosen] at angles
  have internal (v : C.Vertex Set.univ) (member : v ∈ chosen) :
      ¬ C.IsBoundaryVertex Set.univ v := by
    have reaches := ((frontier.mem_processedDescendants vertex v).mp member).2
    exact fun boundary => P.descendant_nonroot nonroot reaches (roots.symm ▸ boundary)
  have original_sum : (∑ v ∈ chosen, C.totalAngle Set.univ v) =
      chosen.card * (2 * Real.pi) - ∑ v ∈ chosen, C.interiorAngularDefect Set.univ v := by
    calc
      _ = ∑ v ∈ chosen, (2 * Real.pi - C.interiorAngularDefect Set.univ v) := by
        apply Finset.sum_congr rfl
        intro v member
        simp only [interiorAngularDefect, ite_eq_right (internal v member)]
        ring
      _ = _ := by rw [Finset.sum_sub_distrib]; simp only [Finset.sum_const, nsmul_eq_mul]
  have term (w : C.Vertex retain) :
      (if C.vertexForgetCuts (Set.subset_univ _) w ∈ frontier.processed ∧
          P.Ancestor (C.vertexForgetCuts (Set.subset_univ _) w) vertex then
            C.totalAngle retain w - Real.pi else 0) =
        (if C.vertexForgetCuts (Set.subset_univ _) w ∈ frontier.processed ∧
          P.Ancestor (C.vertexForgetCuts (Set.subset_univ _) w) vertex then
            C.totalAngle retain w else 0) - Real.pi *
        (if C.vertexForgetCuts (Set.subset_univ _) w ∈ frontier.processed ∧
          P.Ancestor (C.vertexForgetCuts (Set.subset_univ _) w) vertex then 1 else 0) := by
    split_ifs <;> ring
  dsimp only [retain, chosen] at term angles original_sum
  simp only [term, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [angles, original_sum, copies]
  ring

include roots in
open Classical in
/-- Apply that identity to the actual covering intermediate bank contour, whose vertices
are automatically processed. Its original subtree turn is exactly the spent curvature sum. -/
theorem sum_processed_contour_subtree_turn (vertex : C.Vertex Set.univ)
    (nonroot : vertex ∉ P.roots) (processed : vertex ∈ frontier.processed) :
    (∑ i : Fin (Q.length + 1),
      if P.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
          (C.boundaryEndVertex (C.processedParentRetain S frontier) (Q.cycle.point i))) vertex then
        C.totalAngle (C.processedParentRetain S frontier)
          (C.boundaryEndVertex (C.processedParentRetain S frontier) (Q.cycle.point i)) - Real.pi
      else 0) =
      Real.pi - ∑ v ∈ frontier.processedDescendants vertex, C.interiorAngularDefect Set.univ v := by
  classical
  let retain := C.processedParentRetain S frontier
  let weight (w : C.Vertex retain) : ℝ :=
    if C.vertexForgetCuts (Set.subset_univ _) w ∈ frontier.processed ∧
      P.Ancestor (C.vertexForgetCuts (Set.subset_univ _) w) vertex then
        C.totalAngle retain w - Real.pi else 0
  have zero_internal (w : C.Vertex retain) (internal : ¬ C.IsBoundaryVertex retain w) :
      weight w = 0 := by
    apply ite_eq_right
    intro both
    exact internal (C.processedCut_boundary_of_processed S frontier roots w both.1)
  have incidence := C.sum_boundaryCycle_weighted_vertices retain Q.cycle Q.closes Q.covers
    weight zero_internal
  have on_contour (i : Fin (Q.length + 1)) :
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex retain (Q.cycle.point i)) ∈ frontier.processed :=
    (C.processedCut_isBoundaryVertex_iff S frontier roots _).mp
      (C.boundaryEndAsVertex retain (Q.cycle.point i)).property
  have total := C.sum_processed_subtree_boundary_turn S frontier roots Q vertex nonroot processed
  change (∑ w, weight w) = _ at total
  rw [← incidence] at total
  simpa only [weight, on_contour, true_and] using total

end Unfoldings.TriangleComplex
