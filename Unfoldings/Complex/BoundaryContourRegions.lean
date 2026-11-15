module

public import Unfoldings.Complex.BoundaryContour

/-! Vertex-region changes are read on the actual named banks of any boundary contour. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam} (Q : C.BoundaryContour retain)

/-- Test a vertex region on both actual endpoints of a boundary bank. -/
def BoundaryRegionCrossing (inside : C.Vertex retain → Prop) (bank : C.BoundaryBank retain) :
    Prop :=
  (inside ((C.boundaryGraph retain).left bank).val ∧
    ¬ inside ((C.boundaryGraph retain).right bank).val) ∨
  (inside ((C.boundaryGraph retain).right bank).val ∧
    ¬ inside ((C.boundaryGraph retain).left bank).val)

/-- The bank-crossing test agrees with the actual cyclic contour successor. -/
theorem boundaryRegionCrossing_iff (inside : C.Vertex retain → Prop)
    (i : Fin (Q.length + 1)) :
    C.BoundaryRegionCrossing inside (C.boundaryEndEquiv retain (Q.cycle.point i)).1 ↔
      (inside (C.boundaryEndVertex retain (Q.cycle.point i)) ∧
        ¬ inside (C.boundaryEndVertex retain (Q.cycle.point (finRotate (Q.length + 1) i)))) ∨
      (inside (C.boundaryEndVertex retain (Q.cycle.point (finRotate (Q.length + 1) i))) ∧
        ¬ inside (C.boundaryEndVertex retain (Q.cycle.point i))) := by
  have next := congrArg Subtype.val (C.boundaryCycle_next_vertex retain Q.cycle Q.closes i)
  change C.boundaryEndVertex retain (C.boundaryTurn retain (Q.cycle.point i)) =
    C.boundaryEndVertex retain (Q.cycle.point (finRotate (Q.length + 1) i)) at next
  rw [← next]
  rcases C.boundaryGraph_bank_link retain (Q.cycle.point i) with
    ⟨first, last⟩ | ⟨first, last⟩
  · have first' := congrArg Subtype.val first
    have last' := congrArg Subtype.val last
    change inside _ ∧ ¬ inside _ ∨ inside _ ∧ ¬ inside _ ↔ _
    change C.boundaryEndVertex retain (Q.cycle.point i) = _ at first'
    change C.boundaryEndVertex retain (C.boundaryTurn retain (Q.cycle.point i)) = _ at last'
    rw [first', last']
  · have first' := congrArg Subtype.val first
    have last' := congrArg Subtype.val last
    change inside _ ∧ ¬ inside _ ∨ inside _ ∧ ¬ inside _ ↔ _
    change C.boundaryEndVertex retain (Q.cycle.point i) = _ at first'
    change C.boundaryEndVertex retain (C.boundaryTurn retain (Q.cycle.point i)) = _ at last'
    rw [first', last']
    exact or_comm

end Unfoldings.TriangleComplex
