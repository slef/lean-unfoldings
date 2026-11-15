module

public import Unfoldings.Complex.ProcessedSubtreeAngles
public import Unfoldings.Complex.ProcessedSubtreeBanks
public import Unfoldings.Complex.BoundaryRolling
public import Unfoldings.Complex.BoundaryContourRotation
public import Unfoldings.Topology.FiniteCyclicTurns

/-! Exact unreduced current parent-bank headings charge only processed original curvature. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (frontier : P.ParentFrontier)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.processedParentRetain S frontier))

include roots in
open Classical in
/-- Actual contour turns sum to processed subtree curvature minus pi. -/
theorem sum_processed_subtree_contour_turn (e : C.Vertex Set.univ)
    (nonroot : e ∉ P.roots) (processed : e ∈ frontier.processed) :
    (∑ i : Fin (Q.length + 1), if C.ProcessedSubtreeBoundaryInside S frontier Q e i then
      Real.pi - C.totalAngle (C.processedParentRetain S frontier)
        (C.boundaryEndVertex (C.processedParentRetain S frontier) (Q.cycle.point i)) else 0) =
      (∑ v ∈ frontier.processedDescendants e, C.interiorAngularDefect Set.univ v) - Real.pi := by
  classical
  have aggregate : (∑ i : Fin (Q.length + 1),
      if C.ProcessedSubtreeBoundaryInside S frontier Q e i then
        C.totalAngle (C.processedParentRetain S frontier)
          (C.boundaryEndVertex (C.processedParentRetain S frontier) (Q.cycle.point i)) - Real.pi
        else 0) =
      Real.pi - ∑ v ∈ frontier.processedDescendants e, C.interiorAngularDefect Set.univ v :=
    C.sum_processed_contour_subtree_turn S frontier roots Q e nonroot processed
  have negate : (∑ i : Fin (Q.length + 1), if C.ProcessedSubtreeBoundaryInside S frontier Q e i then
      Real.pi - C.totalAngle (C.processedParentRetain S frontier)
        (C.boundaryEndVertex (C.processedParentRetain S frontier) (Q.cycle.point i)) else 0) =
      -(∑ i : Fin (Q.length + 1), if C.ProcessedSubtreeBoundaryInside S frontier Q e i then
        C.totalAngle (C.processedParentRetain S frontier)
          (C.boundaryEndVertex (C.processedParentRetain S frontier) (Q.cycle.point i)) - Real.pi
        else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [negate, aggregate]
  ring

include roots in
/-- The reversed exit has real heading equal to processed subtree curvature. -/
theorem processed_subtree_rollHeading_of_first_entry (e : C.Vertex Set.univ)
    (nonroot : e ∉ P.roots) (processed : e ∈ frontier.processed)
    (leave : Fin (Q.length + 1))
    (enters : ¬ C.ProcessedSubtreeBoundaryInside S frontier Q e 0 ∧
      C.ProcessedSubtreeBoundaryInside S frontier Q e (finRotate (Q.length + 1) 0))
    (leaves : C.ProcessedSubtreeBoundaryInside S frontier Q e leave ∧
      ¬ C.ProcessedSubtreeBoundaryInside S frontier Q e (finRotate (Q.length + 1) leave))
    (stable : ∀ i, i ≠ 0 → i ≠ leave →
      (C.ProcessedSubtreeBoundaryInside S frontier Q e (finRotate (Q.length + 1) i) ↔
        C.ProcessedSubtreeBoundaryInside S frontier Q e i)) :
    C.boundaryRollHeading Q leave + Real.pi =
      ∑ v ∈ frontier.processedDescendants e, C.interiorAngularDefect Set.univ v := by
  have comparison := partialSum_turns_eq_region_sum
    (fun i => Real.pi - C.totalAngle (C.processedParentRetain S frontier)
      (C.boundaryEndVertex (C.processedParentRetain S frontier) (Q.cycle.point i)))
    (C.ProcessedSubtreeBoundaryInside S frontier Q e) leave enters leaves stable
  change C.boundaryRollHeading Q leave = _ at comparison
  rw [C.sum_processed_subtree_contour_turn S frontier roots Q e nonroot processed] at comparison
  linarith

include roots in
/-- Choose the actual entering parent bank and obtain its exact real subtree exit heading. -/
theorem exists_processed_subtree_real_bank_heading (e : C.Vertex Set.univ)
    (nonroot : e ∉ P.roots) (processed : e ∈ frontier.processed) :
    ∃ first leave : Fin (Q.length + 1), ∃ side : Bool,
      (C.boundaryEndEquiv (C.processedParentRetain S frontier) (Q.cycle.point first)).1 =
        C.relativeCutBank (C.processedParentRetain S frontier) Set.univ
          (C.processedParentCut S frontier e nonroot processed) side ∧
      (C.boundaryEndEquiv (C.processedParentRetain S frontier)
        ((Q.rotate C first).cycle.point leave)).1 =
        C.relativeCutBank (C.processedParentRetain S frontier) Set.univ
          (C.processedParentCut S frontier e nonroot processed) (!side) ∧
      C.boundaryRollHeading (Q.rotate C first) leave + Real.pi =
        ∑ v ∈ frontier.processedDescendants e, C.interiorAngularDefect Set.univ v := by
  obtain ⟨first, last, different, enters, leaves, stable⟩ :=
    C.exists_oriented_processed_subtree_exits S frontier roots Q e nonroot processed
  let R := Q.rotate C first
  have at_zero : ¬ C.ProcessedSubtreeBoundaryInside S frontier R e 0 := by
    change ¬ C.ProcessedSubtreeBoundaryInside S frontier Q e (finCycle first 0)
    simpa only [finCycle_apply, zero_add] using enters.1
  have after_zero :
      C.ProcessedSubtreeBoundaryInside S frontier R e (finRotate (Q.length + 1) 0) := by
    change C.ProcessedSubtreeBoundaryInside S frontier Q e
      (finCycle first (finRotate (Q.length + 1) 0))
    have rotated : finCycle first (finRotate (Q.length + 1) 0) =
        finRotate (Q.length + 1) first := by
      simp only [finCycle_apply, finRotate_apply]
      abel
    rw [rotated]
    exact enters.2
  obtain ⟨entry, leave, distinct, entry_data, leave_data, unchanged⟩ :=
    C.exists_oriented_processed_subtree_exits S frontier roots R e nonroot processed
  have entry_eq_zero : entry = 0 := by
    by_contra entry_ne
    have leave_ne : (0 : Fin (Q.length + 1)) ≠ leave := by
      intro equal
      exact at_zero (equal.symm ▸ leave_data.1)
    exact at_zero ((unchanged 0 (Ne.symm entry_ne) leave_ne).mp after_zero)
  subst entry
  have heading := C.processed_subtree_rollHeading_of_first_entry S frontier roots R e nonroot
    processed leave
    entry_data leave_data unchanged
  have entrance := (C.processed_subtree_crossing_iff S frontier roots e nonroot processed _).mp
    ((C.boundaryRegionCrossing_iff Q
      (fun w => P.Ancestor (C.vertexForgetCuts (Set.subset_univ _) w) e) first).mpr
      (Or.inr ⟨enters.2, enters.1⟩))
  have exit := (C.processed_subtree_crossing_iff S frontier roots e nonroot processed _).mp
    ((C.boundaryRegionCrossing_iff R
      (fun w => P.Ancestor (C.vertexForgetCuts (Set.subset_univ _) w) e) leave).mpr
      (Or.inl leave_data))
  obtain ⟨a, first_named⟩ := entrance
  obtain ⟨b, last_named⟩ := exit
  have named_zero :
      (C.boundaryEndEquiv (C.processedParentRetain S frontier) (R.cycle.point 0)).1 =
      C.relativeCutBank (C.processedParentRetain S frontier) Set.univ
          (C.processedParentCut S frontier e nonroot processed) a := by
    change (C.boundaryEndEquiv (C.processedParentRetain S frontier) R.cycle.first).1 = _
    rw [BoundaryContour.rotate_first]
    exact first_named
  have different_sides : b ≠ a := by
    intro equal
    have banks := named_zero.trans (equal ▸ last_named).symm
    have same := C.boundaryChain_banks_injective (C.processedParentRetain S frontier)
      R.cycle banks
    exact entry_data.1 (same.symm ▸ leave_data.1)
  have opposite : b = !a := by
    cases a <;> cases b <;> first | rfl | exact (different_sides rfl).elim
  exact ⟨first, leave, a, first_named, opposite ▸ last_named, heading⟩

end Unfoldings.TriangleComplex
