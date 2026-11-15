module

public import Unfoldings.Complex.SelectedSubtreeAngles
public import Unfoldings.Complex.SubtreeContour
public import Unfoldings.Complex.BoundaryRolling
public import Unfoldings.Complex.BoundaryContourRotation
public import Unfoldings.Topology.FiniteCyclicTurns

/-! Exact unreduced subtree bank heading from the actual original cut fans. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))

include roots in
open Classical in
/-- Actual contour turns, including branching copies, sum to subtree curvature minus pi. -/
theorem sum_subtree_contour_turn (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots) :
    (∑ i : Fin (Q.length + 1), if C.SubtreeBoundaryInside S Q.cycle e i then
      Real.pi - C.totalAngle (C.selectedRetain S)
        (C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point i)) else 0) =
      (∑ v ∈ P.descendants e, C.interiorAngularDefect Set.univ v) - Real.pi := by
  classical
  have aggregate : (∑ i : Fin (Q.length + 1),
      if C.SubtreeBoundaryInside S Q.cycle e i then
        C.totalAngle (C.selectedRetain S)
          (C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point i)) - Real.pi else 0) =
      Real.pi - ∑ v ∈ P.descendants e, C.interiorAngularDefect Set.univ v :=
    (C.sum_boundaryCycle_vertices (C.selectedRetain S) Q.cycle Q.closes Q.covers
    (C.selectedCut_all_vertices_boundary S roots) _).trans
      (C.sum_subtree_boundary_turn S roots Q.cycle Q.closes Q.covers e nonroot)
  have negate : (∑ i : Fin (Q.length + 1), if C.SubtreeBoundaryInside S Q.cycle e i then
      Real.pi - C.totalAngle (C.selectedRetain S)
        (C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point i)) else 0) =
      -(∑ i : Fin (Q.length + 1), if C.SubtreeBoundaryInside S Q.cycle e i then
        C.totalAngle (C.selectedRetain S)
          (C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point i)) - Real.pi else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [negate, aggregate]
  ring

include roots in
/-- Starting on the entering bank, the reversed exit has real heading equal to curvature. -/
theorem subtree_rollHeading_of_first_entry (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots)
    (leave : Fin (Q.length + 1))
    (enters : ¬ C.SubtreeBoundaryInside S Q.cycle e 0 ∧
      C.SubtreeBoundaryInside S Q.cycle e (finRotate (Q.length + 1) 0))
    (leaves : C.SubtreeBoundaryInside S Q.cycle e leave ∧
      ¬ C.SubtreeBoundaryInside S Q.cycle e (finRotate (Q.length + 1) leave))
    (stable : ∀ i, i ≠ 0 → i ≠ leave →
      (C.SubtreeBoundaryInside S Q.cycle e (finRotate (Q.length + 1) i) ↔
        C.SubtreeBoundaryInside S Q.cycle e i)) :
    C.boundaryRollHeading Q leave + Real.pi =
      ∑ v ∈ P.descendants e, C.interiorAngularDefect Set.univ v := by
  have comparison := partialSum_turns_eq_region_sum
    (fun i => Real.pi - C.totalAngle (C.selectedRetain S)
      (C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point i)))
    (C.SubtreeBoundaryInside S Q.cycle e) leave enters leaves stable
  change C.boundaryRollHeading Q leave = _ at comparison
  rw [C.sum_subtree_contour_turn S roots Q e nonroot] at comparison
  linarith

include roots in
/-- Choose the actual entering parent bank and obtain its exact real subtree exit heading. -/
theorem exists_subtree_real_bank_heading (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots) :
    ∃ first leave : Fin (Q.length + 1), ∃ side : Bool,
      (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point first)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) side ∧
      (C.boundaryEndEquiv (C.selectedRetain S) ((Q.rotate C first).cycle.point leave)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) (!side) ∧
      C.boundaryRollHeading (Q.rotate C first) leave + Real.pi =
        ∑ v ∈ P.descendants e, C.interiorAngularDefect Set.univ v := by
  obtain ⟨first, last, different, enters, leaves, stable⟩ :=
    C.exists_oriented_subtree_exits S roots Q.cycle Q.closes Q.covers e nonroot
  let R := Q.rotate C first
  have at_zero : ¬ C.SubtreeBoundaryInside S R.cycle e 0 := by
    change ¬ C.SubtreeBoundaryInside S Q.cycle e (finCycle first 0)
    simpa only [finCycle_apply, zero_add] using enters.1
  have after_zero : C.SubtreeBoundaryInside S R.cycle e (finRotate (Q.length + 1) 0) := by
    change C.SubtreeBoundaryInside S Q.cycle e
      (finCycle first (finRotate (Q.length + 1) 0))
    have rotated : finCycle first (finRotate (Q.length + 1) 0) =
        finRotate (Q.length + 1) first := by
      simp only [finCycle_apply, finRotate_apply]
      abel
    rw [rotated]
    exact enters.2
  obtain ⟨entry, leave, distinct, entry_data, leave_data, unchanged⟩ :=
    C.exists_oriented_subtree_exits S roots R.cycle R.closes R.covers e nonroot
  have entry_eq_zero : entry = 0 := by
    by_contra entry_ne
    have leave_ne : (0 : Fin (Q.length + 1)) ≠ leave := by
      intro equal
      exact at_zero (equal.symm ▸ leave_data.1)
    exact at_zero ((unchanged 0 (Ne.symm entry_ne) leave_ne).mp after_zero)
  subst entry
  have heading := C.subtree_rollHeading_of_first_entry S roots R e nonroot leave
    entry_data leave_data unchanged
  have entrance := (C.subtreeCrossingBank_iff S roots e nonroot _).mp
    ((C.subtree_boundary_change_iff S Q.cycle Q.closes e first).mpr
      (Or.inr ⟨enters.2, enters.1⟩))
  have exit := (C.subtreeCrossingBank_iff S roots e nonroot _).mp
    ((C.subtree_boundary_change_iff S R.cycle R.closes e leave).mpr (Or.inl leave_data))
  obtain ⟨a, first_named⟩ := entrance
  obtain ⟨b, last_named⟩ := exit
  have named_zero : (C.boundaryEndEquiv (C.selectedRetain S) (R.cycle.point 0)).1 =
      C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) a := by
    change (C.boundaryEndEquiv (C.selectedRetain S) R.cycle.first).1 = _
    rw [BoundaryContour.rotate_first]
    exact first_named
  have different_sides : b ≠ a := by
    intro equal
    have banks := named_zero.trans (equal ▸ last_named).symm
    have same := C.boundaryChain_banks_injective (C.selectedRetain S) R.cycle banks
    exact entry_data.1 (same.symm ▸ leave_data.1)
  have opposite : b = !a := by
    cases a <;> cases b <;> first | rfl | exact (different_sides rfl).elim
  exact ⟨first, leave, a, first_named, opposite ▸ last_named, heading⟩

end Unfoldings.TriangleComplex
