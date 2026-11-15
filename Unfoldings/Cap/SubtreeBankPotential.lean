module

public import Unfoldings.Cap.SubtreeRealHeading
public import Unfoldings.Topology.SubtreePotentialWeights

/-! Actual real parent-bank headings cancel through nested subtrees before curvature is bounded. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))

include K roots in
open Classical in
/-- Choose actual opposite parent-bank rolls whose signed membership-change potential has
magnitude at most total curvature for every selected original vertex set. -/
theorem exists_subtree_bank_potential_bounds :
    ∃ first leave : {e : C.Vertex Set.univ // e ∉ P.roots} → Fin (Q.length + 1),
      ∃ side : {e : C.Vertex Set.univ // e ∉ P.roots} → Bool,
      (∀ e, (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point (first e))).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ
          (C.selectedParentCut S e.val e.property) (side e) ∧
        (C.boundaryEndEquiv (C.selectedRetain S) ((Q.rotate C (first e)).cycle.point (leave e))).1 =
          C.relativeCutBank (C.selectedRetain S) Set.univ
            (C.selectedParentCut S e.val e.property) (!(side e))) ∧
      ∀ selected : Set (C.Vertex Set.univ),
        |∑ e : {e : C.Vertex Set.univ // e ∉ P.roots},
          ((if e.val ∈ selected then (1 : ℝ) else 0) -
            (if P.parent e.val ∈ selected then 1 else 0)) *
              (C.boundaryRollHeading (Q.rotate C (first e)) (leave e) + Real.pi)| ≤
          C.totalInteriorAngularDefect Set.univ := by
  classical
  choose first leave side entrance exit heading using
    (fun e : {e : C.Vertex Set.univ // e ∉ P.roots} =>
      C.exists_subtree_real_bank_heading S roots Q e.val e.property)
  refine ⟨first, leave, side, fun e => ⟨entrance e, exit e⟩, fun selected => ?_⟩
  have reindex : (∑ e : {e : C.Vertex Set.univ // e ∉ P.roots},
      ((if e.val ∈ selected then (1 : ℝ) else 0) -
        (if P.parent e.val ∈ selected then 1 else 0)) *
          (C.boundaryRollHeading (Q.rotate C (first e)) (leave e) + Real.pi)) =
      ∑ e : C.Vertex Set.univ, if e ∉ P.roots then
        ((if e ∈ selected then (1 : ℝ) else 0) -
          (if P.parent e ∈ selected then 1 else 0)) *
            (∑ v ∈ P.descendants e, C.interiorAngularDefect Set.univ v) else 0 := by
    simp_rw [heading]
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (p := fun e : C.Vertex Set.univ => e ∉ P.roots)
      (Finset.univ.filter (fun e => e ∉ P.roots)) (by simp)
      (fun e => ((if e ∈ selected then (1 : ℝ) else 0) -
        (if P.parent e ∈ selected then 1 else 0)) *
          (∑ v ∈ P.descendants e, C.interiorAngularDefect Set.univ v))).symm
  rw [reindex]
  exact P.abs_sum_subtree_membership_changes_le
    (fun v => C.interiorAngularDefect Set.univ v) K.interiorCurvature_nonneg selected

end Unfoldings.ConvexCap
