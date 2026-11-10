module

public import Unfoldings.Complex.SelectedIncidence
public import Unfoldings.Complex.AngleCutSums
public import Unfoldings.Complex.Curvature

/-!
# Exact angular accounting around branching descendant subtrees

All actual cut copies above a nonroot descendant subtree have aggregate
boundary turn pi minus the subtree's original intrinsic angular defect.
The bank rotation and its global orientation are separate geometric claims.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  {n : ℕ} (cycle : (C.boundarySystem (C.selectedRetain S)).Chain n)
  (closes : C.boundaryMate (C.selectedRetain S)
    (C.boundaryTurn (C.selectedRetain S) cycle.last) = cycle.first)
  (covers : ∀ p, cycle.Visited p)

include roots cycle closes covers in
open scoped Classical in
/-- Branching creates exactly twice as many descendant copies as original vertices, minus one. -/
theorem sum_subtree_vertex_copies (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots) :
    (∑ w : C.Vertex (C.selectedRetain S),
      if P.Ancestor (C.vertexForgetCuts (Set.subset_univ _) w) e then (1 : ℝ) else 0) =
        2 * (P.descendants e).card - 1 := by
  classical
  have counted := C.sum_selected_vertex_weights S roots cycle closes covers
    (fun v => if P.Ancestor v e then 1 else 0) (by
      intro v root
      rw [ite_eq_right (fun reaches => P.descendant_nonroot nonroot reaches root)])
  exact counted.trans (P.sum_descendant_incidence e nonroot)

include roots cycle closes covers in
open scoped Classical in
/-- Aggregate actual boundary turn for any branching descendant subtree. -/
theorem sum_subtree_boundary_turn (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots) :
    (∑ w : C.Vertex (C.selectedRetain S),
      if P.Ancestor (C.vertexForgetCuts (Set.subset_univ _) w) e then
        C.totalAngle (C.selectedRetain S) w - Real.pi else 0) =
      Real.pi - ∑ v ∈ P.descendants e, C.interiorAngularDefect Set.univ v := by
  classical
  have copies := C.sum_subtree_vertex_copies S roots cycle closes covers e nonroot
  have angles := C.sum_totalAngle_over_copies (Set.subset_univ (C.selectedRetain S))
    (P.descendants e)
  simp only [P.mem_descendants] at angles
  have internal (v : C.Vertex Set.univ) (member : v ∈ P.descendants e) :
      ¬ C.IsBoundaryVertex Set.univ v := by
    have nonroot_v := P.descendant_nonroot nonroot ((P.mem_descendants v e).mp member)
    exact fun boundary => nonroot_v (roots.symm ▸ boundary)
  have original_sum : (∑ v ∈ P.descendants e, C.totalAngle Set.univ v) =
      (P.descendants e).card * (2 * Real.pi) -
        ∑ v ∈ P.descendants e, C.interiorAngularDefect Set.univ v := by
    calc
      _ = ∑ v ∈ P.descendants e, (2 * Real.pi - C.interiorAngularDefect Set.univ v) := by
        apply Finset.sum_congr rfl
        intro v member
        simp only [interiorAngularDefect, ite_eq_right (internal v member)]
        ring
      _ = _ := by rw [Finset.sum_sub_distrib]; simp only [Finset.sum_const, nsmul_eq_mul]
  have term (w : C.Vertex (C.selectedRetain S)) :
      (if P.Ancestor (C.vertexForgetCuts (Set.subset_univ _) w) e then
        C.totalAngle (C.selectedRetain S) w - Real.pi else 0) =
      (if P.Ancestor (C.vertexForgetCuts (Set.subset_univ _) w) e then
        C.totalAngle (C.selectedRetain S) w else 0) -
      Real.pi * (if P.Ancestor (C.vertexForgetCuts (Set.subset_univ _) w) e then 1 else 0) := by
    split_ifs <;> ring
  simp only [term, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [angles, original_sum, copies]
  ring

end Unfoldings.TriangleComplex
