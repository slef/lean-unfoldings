module

public import Unfoldings.Complex.BoundaryCycleEnumeration

/-!
# Weighted boundary incidence

The two ends of the actual banks count each vertex copy twice along a covering
cycle. Weights may select only the copies lying above a chosen original region.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) [Fintype (C.BoundaryBank retain)]
  {n : ℕ} (cycle : (C.boundarySystem retain).Chain n)
  (closes : C.boundaryMate retain (C.boundaryTurn retain cycle.last) = cycle.first)
  (covers : ∀ p, cycle.Visited p)

include closes covers in
/-- Endpoint incidence computed along the actual boundary cycle. -/
theorem sum_boundaryBank_incidence (weight : C.BoundaryVertex retain → ℝ) :
    (∑ bank : C.BoundaryBank retain,
      (weight ((C.boundaryGraph retain).left bank) +
        weight ((C.boundaryGraph retain).right bank))) =
      2 * ∑ i, weight (C.boundaryEndAsVertex retain (cycle.point i)) := by
  let bank := C.boundaryCycleBankEquiv retain cycle covers
  have endpoint_sum (i : Fin (n + 1)) :
      weight ((C.boundaryGraph retain).left (bank i)) +
        weight ((C.boundaryGraph retain).right (bank i)) =
      weight (C.boundaryEndAsVertex retain (cycle.point i)) +
        weight (C.boundaryEndAsVertex retain (cycle.point (finRotate (n + 1) i))) := by
    change weight ((C.boundaryGraph retain).left
      (C.boundaryEndEquiv retain (cycle.point i)).1) +
      weight ((C.boundaryGraph retain).right (C.boundaryEndEquiv retain (cycle.point i)).1) = _
    rw [← C.boundaryCycle_next_vertex retain cycle closes]
    rcases C.boundaryGraph_bank_link retain (cycle.point i) with
      ⟨first, last⟩ | ⟨first, last⟩
    · rw [← first, ← last]
    · rw [← last, ← first, add_comm]
  calc
    _ = ∑ i, (weight ((C.boundaryGraph retain).left (bank i)) +
        weight ((C.boundaryGraph retain).right (bank i))) := (bank.sum_comp _).symm
    _ = (∑ i, weight (C.boundaryEndAsVertex retain (cycle.point i))) +
        ∑ i, weight (C.boundaryEndAsVertex retain (cycle.point (finRotate (n + 1) i))) := by
      simp only [endpoint_sum, Finset.sum_add_distrib]
    _ = _ := by
      rw [Equiv.sum_comp (finRotate (n + 1))
        (fun i => weight (C.boundaryEndAsVertex retain (cycle.point i)))]
      ring

include cycle closes covers in
/-- When all copies lie on the boundary, incidence counts all actual cut vertices twice. -/
theorem sum_boundaryBank_incidence_all (all_boundary : ∀ v, C.IsBoundaryVertex retain v)
    (weight : C.Vertex retain → ℝ) :
    (∑ bank : C.BoundaryBank retain,
      (weight ((C.boundaryGraph retain).left bank).val +
        weight ((C.boundaryGraph retain).right bank).val)) =
      2 * ∑ v, weight v := by
  have incidence := C.sum_boundaryBank_incidence retain cycle closes covers
    (fun v => weight v.val)
  rw [show (∑ i, weight (C.boundaryEndAsVertex retain (cycle.point i)).val) = ∑ v, weight v
    from C.sum_boundaryCycle_vertices retain cycle closes covers all_boundary weight] at incidence
  exact incidence

end Unfoldings.TriangleComplex
