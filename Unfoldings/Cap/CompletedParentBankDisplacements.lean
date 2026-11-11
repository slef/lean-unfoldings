module

public import Unfoldings.Cap.CompletedParentBankOpening
public import Unfoldings.Development.BoundaryDisplacements

/-! Actual subtree entrance, exit, and displacement identities for completed roof banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.ParentBankOpening

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain}
  {e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}} (O : N.ParentBankOpening
    D e)

theorem enter_ne_leave : O.enter ≠ O.leave := by
  intro same
  exact O.outside (same ▸ O.inside)

/-- A named entrance really crosses from the parent side to the descendant side. -/
theorem enters : ¬ C.SubtreeBoundaryInside N.spanningCompletion.selection N.completedContour.cycle
  e.val O.enter ∧
    C.SubtreeBoundaryInside N.spanningCompletion.selection N.completedContour.cycle e.val
      (finRotate (N.completedContour.length + 1) O.enter) := by
  have crossing := (C.subtreeCrossingBank_iff N.spanningCompletion.selection
    N.spanningCompletion.roots_eq e.val e.property _).mpr
    ⟨O.side, O.first_named⟩
  have changes := (C.subtree_boundary_change_iff N.spanningCompletion.selection
    N.completedContour.cycle
    N.completedContour.closes e.val O.enter).mp crossing
  rcases changes with first | last
  · exact (O.outside first.1).elim
  · exact ⟨last.2, last.1⟩

/-- A named exit really crosses from the descendant side to the parent side. -/
theorem leaves : C.SubtreeBoundaryInside N.spanningCompletion.selection N.completedContour.cycle
  e.val O.leave ∧
    ¬ C.SubtreeBoundaryInside N.spanningCompletion.selection N.completedContour.cycle e.val
      (finRotate (N.completedContour.length + 1) O.leave) := by
  have crossing := (C.subtreeCrossingBank_iff N.spanningCompletion.selection
    N.spanningCompletion.roots_eq e.val e.property _).mpr
    ⟨!O.side, O.last_named⟩
  have changes := (C.subtree_boundary_change_iff N.spanningCompletion.selection
    N.completedContour.cycle
    N.completedContour.closes e.val O.leave).mp crossing
  rcases changes with first | last
  · exact first
  · exact (last.2 O.inside).elim

theorem stable (i : Fin (N.completedContour.length + 1))
    (not_enter : i ≠ O.enter) (not_leave : i ≠ O.leave) :
    C.SubtreeBoundaryInside N.spanningCompletion.selection N.completedContour.cycle e.val
        (finRotate (N.completedContour.length + 1) i) ↔
      C.SubtreeBoundaryInside N.spanningCompletion.selection N.completedContour.cycle e.val i := by
  classical
  by_contra changes
  have crossing := (C.subtree_boundary_change_iff N.spanningCompletion.selection
    N.completedContour.cycle
    N.completedContour.closes e.val i).mpr (by tauto)
  obtain ⟨side, named⟩ :=
    (C.subtreeCrossingBank_iff N.spanningCompletion.selection N.spanningCompletion.roots_eq e.val
      e.property _).mp crossing
  have alternatives : side = O.side ∨ side = !O.side := by cases side <;> cases O.side <;> simp
  rcases alternatives with same | same
  · exact not_enter (C.boundaryChain_banks_injective N.completedRetain N.completedContour.cycle
      (named.trans (same ▸ O.first_named).symm))
  · exact not_leave (C.boundaryChain_banks_injective N.completedRetain N.completedContour.cycle
      (named.trans (same ▸ O.last_named).symm))

open scoped Classical in
/-- The parent-copy gap equals the entrance vector plus all descendant-starting bank vectors. -/
theorem parent_position_gap :
    D.boundaryPosition (C.boundaryTurn N.completedRetain (N.completedContour.cycle.point O.leave)) -
        D.boundaryPosition (N.completedContour.cycle.point O.enter) =
      D.boundaryRay (N.completedContour.cycle.point O.enter) +
        ∑ i : Fin (N.completedContour.length + 1),
          if C.SubtreeBoundaryInside N.spanningCompletion.selection N.completedContour.cycle e.val
            i then
            D.boundaryRay (N.completedContour.cycle.point i) else 0 := by
  have gap := displacement_gap_of_two_region_exits
    (finRotate (N.completedContour.length + 1))
    (C.SubtreeBoundaryInside N.spanningCompletion.selection N.completedContour.cycle e.val)
    (fun i => D.boundaryPosition (N.completedContour.cycle.point i))
    O.enter O.leave O.enter_ne_leave O.enters O.leaves O.stable
  simp only [← D.boundaryRay_eq_cycle_displacement N.completedContour.cycle
    N.completedContour.closes] at gap
  have next := congrArg Subtype.val (C.boundaryCycle_next_vertex N.completedRetain
    N.completedContour.cycle N.completedContour.closes O.leave)
  change C.boundaryEndVertex N.completedRetain
      (C.boundaryTurn N.completedRetain (N.completedContour.cycle.point O.leave)) =
    C.boundaryEndVertex N.completedRetain
      (N.completedContour.cycle.point (finRotate (N.completedContour.length + 1) O.leave)) at next
  simpa only [FacewiseDevelopment.boundaryPosition, next] using gap

end Unfoldings.ConvexCap.RadialCutForest.ParentBankOpening
