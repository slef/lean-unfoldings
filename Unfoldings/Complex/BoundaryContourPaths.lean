module

public import Unfoldings.Complex.DirectedBoundaryPath
public import Unfoldings.Complex.BoundaryContourRotation

/-! A complete directed contour parametrizes every actual boundary bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam}

/-- Either endpoint order parametrizes the whole original bank. -/
theorem bankParameterFromEnd_surjective (bank : C.BoundaryBank retain) (side : Bool) :
    Function.Surjective (C.bankParameterFromEnd bank side) := by
  intro x
  have member := x.property
  cases side
  · change x.val ∈ segment ℝ ((C.triangle bank.val.face).vertex bank.val.edge)
      ((C.triangle bank.val.face).vertex (Triangle.next bank.val.edge)) at member
    rw [segment_eq_image_lineMap] at member
    obtain ⟨t, ht, equal⟩ := member
    exact ⟨⟨t, ht⟩, Subtype.ext equal⟩
  · change x.val ∈ segment ℝ ((C.triangle bank.val.face).vertex bank.val.edge)
      ((C.triangle bank.val.face).vertex (Triangle.next bank.val.edge)) at member
    rw [segment_symm, segment_eq_image_lineMap] at member
    obtain ⟨t, ht, equal⟩ := member
    exact ⟨⟨t, ht⟩, Subtype.ext equal⟩

/-- Every boundary point occurs on one of the contour's actual directed paths. -/
theorem BoundaryContour.exists_directedBoundaryPath (Q : C.BoundaryContour retain)
    {x : C.Realization retain} (boundary : x ∈ C.bankBoundary retain) :
    ∃ (i : Fin (Q.length + 1)) (t : unitInterval),
      C.directedBoundaryPath (Q.cycle.point i) t = x := by
  obtain ⟨bank, y, rfl⟩ := Set.mem_iUnion.mp boundary
  obtain ⟨i, same⟩ := (C.boundaryCycleBankEquiv retain Q.cycle Q.covers).surjective bank
  change (C.boundaryEndEquiv retain (Q.cycle.point i)).1 = bank at same
  subst bank
  obtain ⟨t, equal⟩ := C.bankParameterFromEnd_surjective
    (C.boundaryEndEquiv retain (Q.cycle.point i)).1
    (C.boundaryEndEquiv retain (Q.cycle.point i)).2 y
  exact ⟨i, t, congrArg (C.bankMap retain _) equal⟩

/-- Strictly inside a directed bank, the actual intrinsic point is never a vertex. -/
theorem directedBoundaryPath_ne_vertexPoint (p : C.BoundaryEnd retain) (t : unitInterval)
    (positive : 0 < t.val) (small : t.val < 1) (w : C.Vertex retain) :
    C.directedBoundaryPath p t ≠ C.vertexPoint retain w := by
  intro equal
  have regular := C.bankParameterFromEnd_nonvertex (C.boundaryEndEquiv retain p).1
    (C.boundaryEndEquiv retain p).2 t positive small
  apply regular
  exact (C.mem_range_vertexPoint_iff retain _).mp ⟨w, equal.symm⟩

end Unfoldings.TriangleComplex
