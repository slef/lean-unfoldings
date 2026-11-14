module

public import Unfoldings.Complex.BoundaryContour

/-! Reindex actual boundary contours without changing their banks or cyclic orientation. -/

@[expose] public section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam} (Q : C.BoundaryContour retain)

/-- Boundary adjacency holds across the final bank as well as inside the enumeration. -/
theorem BoundaryContour.next_cyclic (i : Fin (Q.length + 1)) :
    C.boundaryMate retain (C.boundaryTurn retain (Q.cycle.point i)) =
      Q.cycle.point (finRotate (Q.length + 1) i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [finRotate_last]
    exact Q.closes
  · rw [show finRotate (Q.length + 1) j.castSucc = j.succ from finRotate_of_lt j.isLt]
    exact Q.cycle.next j

/-- A new starting bank keeps the actual directed contour and every original bank label. -/
def BoundaryContour.rotate (first : Fin (Q.length + 1)) : C.BoundaryContour retain where
  length := Q.length
  cycle := {
    point := fun i => Q.cycle.point (finCycle first i)
    injective := Q.cycle.injective.comp (finCycle first).injective
    disjoint := fun i j => Q.cycle.disjoint _ _
    next := fun i => by
      change C.boundaryMate retain
        (C.boundaryTurn retain (Q.cycle.point (finCycle first i.castSucc))) =
          Q.cycle.point (finCycle first i.succ)
      rw [Q.next_cyclic C]
      congr 1
      simp only [finRotate_apply, finCycle_apply]
      rw [← Fin.coeSucc_eq_succ]
      abel }
  closes := by
    change C.boundaryMate retain
      (C.boundaryTurn retain (Q.cycle.point (finCycle first (Fin.last Q.length)))) =
      Q.cycle.point (finCycle first 0)
    rw [Q.next_cyclic C]
    congr 1
    rw [finRotate_apply, finCycle_apply, finCycle_apply, zero_add]
    have wrap : (Fin.last Q.length : Fin (Q.length + 1)) + 1 = 0 := by
      rw [← finRotate_apply, finRotate_last]
    calc
      Fin.last Q.length + first + 1 = (Fin.last Q.length + 1) + first := by abel
      _ = first := by rw [wrap, zero_add]
  covers := fun p => by
    obtain ⟨i, same⟩ := Q.covers p
    refine ⟨(finCycle first).symm i, ?_⟩
    change p = Q.cycle.point (finCycle first ((finCycle first).symm i)) ∨
      p = (C.boundarySystem retain).turn
        (Q.cycle.point (finCycle first ((finCycle first).symm i)))
    simpa only [Equiv.apply_symm_apply] using same

@[simp] theorem BoundaryContour.rotate_point (first i : Fin (Q.length + 1)) :
    (Q.rotate C first).cycle.point i = Q.cycle.point (i + first) := rfl

@[simp] theorem BoundaryContour.rotate_first (first : Fin (Q.length + 1)) :
    (Q.rotate C first).cycle.first = Q.cycle.point first := by
  change Q.cycle.point (0 + first) = _
  rw [zero_add]

/-- Reindexing the contour does not change any total bank weight. -/
theorem BoundaryContour.sum_rotate {M : Type*} [AddCommMonoid M]
    (first : Fin (Q.length + 1)) (weight : C.BoundaryEnd retain → M) :
    (∑ i, weight ((Q.rotate C first).cycle.point i)) = ∑ i, weight (Q.cycle.point i) :=
  Equiv.sum_comp (finCycle first) (fun i => weight (Q.cycle.point i))

end Unfoldings.TriangleComplex
