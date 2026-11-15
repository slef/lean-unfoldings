module

public import Unfoldings.Complex.BoundaryIncidence

/-! Boundary incidence with weights vanishing at the actual internal vertex copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) {n : ℕ} (cycle : (C.boundarySystem retain).Chain n)
  (closes : C.boundaryMate retain (C.boundaryTurn retain cycle.last) = cycle.first)
  (covers : ∀ p, cycle.Visited p)

include closes covers in
/-- A covering actual contour sums all vertex weights when internal copies have zero weight.
The surface may retain unprocessed curved interior vertices. -/
theorem sum_boundaryCycle_weighted_vertices (weight : C.Vertex retain → ℝ)
    (zero_internal : ∀ w, ¬ C.IsBoundaryVertex retain w → weight w = 0) :
    (∑ i, weight (C.boundaryEndVertex retain (cycle.point i))) = ∑ w, weight w := by
  classical
  let E := C.boundaryCycleVertexEquiv retain cycle closes covers
  have ordered := E.sum_comp (fun v => weight v.val)
  change (∑ i, weight (C.boundaryEndVertex retain (cycle.point i))) =
    ∑ v : C.BoundaryVertex retain, weight v.val at ordered
  rw [ordered]
  have reindex := Finset.sum_subtype (F := inferInstance)
    (p := fun w : C.Vertex retain => C.IsBoundaryVertex retain w)
    (Finset.univ.filter (C.IsBoundaryVertex retain)) (by simp) weight
  rw [← reindex, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w _
  by_cases boundary : C.IsBoundaryVertex retain w
  · simp only [boundary, ite_true]
  · simp only [boundary, ite_false, zero_internal w boundary]

variable [Fintype (C.BoundaryBank retain)]

include closes covers in
/-- Each actual boundary copy is still counted exactly twice when internal weights vanish. -/
theorem sum_boundaryBank_weighted_incidence (weight : C.Vertex retain → ℝ)
    (zero_internal : ∀ w, ¬ C.IsBoundaryVertex retain w → weight w = 0) :
    (∑ bank : C.BoundaryBank retain,
      (weight ((C.boundaryGraph retain).left bank).val +
        weight ((C.boundaryGraph retain).right bank).val)) = 2 * ∑ w, weight w := by
  have counted := C.sum_boundaryBank_incidence retain cycle closes covers (fun w => weight w.val)
  rw [show (∑ i, weight (C.boundaryEndAsVertex retain (cycle.point i)).val) = ∑ w, weight w
    from C.sum_boundaryCycle_weighted_vertices retain cycle closes covers weight zero_internal]
    at counted
  exact counted

end Unfoldings.TriangleComplex
