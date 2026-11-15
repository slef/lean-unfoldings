module

public import Unfoldings.Complex.GermEndpoints
public import Unfoldings.Complex.Links
public import Unfoldings.Complex.BoundaryOrdering

/-! Reverse endpoints of an original edge germ without changing its incident face side. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- This reverses the directed edge; `turnGerm` instead changes edges at the same corner. -/
def edgeReverseGerm (p : C.Germ) : C.Germ := C.germOfEndpoint (C.germEdge p) (!p.2)

@[simp] theorem edgeReverseGerm_edge (p : C.Germ) :
    C.germEdge (C.edgeReverseGerm p) = C.germEdge p := C.germEdge_germOfEndpoint _ _

@[simp] theorem edgeReverseGerm_involutive : Function.Involutive C.edgeReverseGerm := by
  intro p
  simp only [edgeReverseGerm, C.germEdge_germOfEndpoint, C.germOfEndpoint_side,
    Bool.not_not, C.germOfEndpoint_germEdge]

/-- Original seam endpoint transport commutes with reversing the directed edge. -/
theorem GermCrosses.edgeReverse {retain : Set C.Seam} {p q : C.Germ}
    (crossing : C.GermCrosses retain p q) :
    C.GermCrosses retain (C.edgeReverseGerm p) (C.edgeReverseGerm q) := by
  obtain ⟨s, kept, side, flag, rfl, rfl⟩ := crossing
  simp only [edgeReverseGerm, C.germEdge_germOfEndpoint, C.germOfEndpoint_side]
  exact ⟨s, kept, side, !flag, rfl, by rw [C.acrossEndpoint_not]⟩

/-- Across-edge pairing and endpoint reversal commute, including originally unpaired banks. -/
theorem mateGerm_edgeReverse (retain : Set C.Seam) (p : C.Germ) :
    C.mateGerm retain (C.edgeReverseGerm p) = C.edgeReverseGerm (C.mateGerm retain p) := by
  classical
  by_cases boundary : C.IsBoundaryEdge retain (C.germEdge p)
  · have fixed := (C.mateGerm_eq_self_iff retain p).mpr boundary
    have reversed := (C.mateGerm_eq_self_iff retain (C.edgeReverseGerm p)).mpr
      (by simpa only [C.edgeReverseGerm_edge] using boundary)
    rw [fixed, reversed]
  · obtain ⟨q, crossing⟩ := (C.exists_germCrosses_iff retain p).mpr boundary
    rw [C.mateGerm_of_crossing (GermCrosses.edgeReverse C crossing),
      C.mateGerm_of_crossing crossing]

/-- An actual bank's endpoint exchange is this original raw edge reversal. -/
theorem boundaryTurn_raw_edgeReverse {retain : Set C.Seam} (p : C.BoundaryEnd retain) :
    (C.boundaryTurn retain p).val = C.edgeReverseGerm p.val := rfl

end Unfoldings.TriangleComplex
