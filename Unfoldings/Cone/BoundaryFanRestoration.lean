module

public import Unfoldings.Cone.RestoredBoundaryFan
public import Unfoldings.Complex.BoundaryLink

/-! Canonical whole tangent-fan restoration from its two actual surviving boundary banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {small large : Set C.Seam} (inclusion : small ⊆ large)
  (p : C.BoundaryEnd small)
  (first : C.IsBoundaryEdge large (C.germEdge p.val))
  (last : C.IsBoundaryEdge large (C.germEdge (C.boundaryMate small p).val))

include first last in
/-- Both terminal banks determine an intrinsic isometry of entire actual tangent fans,
fixing every point of every original supporting wedge. The covering link is constructed. -/
theorem exists_boundaryFanRestorationIsometry :
    ∃ E : C.TangentFan small (C.boundaryEndVertex small p) ≃ᵢ
      C.TangentFan large (C.vertexForgetCuts inclusion (C.boundaryEndVertex small p)),
      ∀ (q : C.CornerAt small (C.boundaryEndVertex small p))
        (x : C.TangentCell small (C.boundaryEndVertex small p) q),
        E (C.tangentFaceMap small (C.boundaryEndVertex small p) q x) =
          C.tangentFaceMap large (C.vertexForgetCuts inclusion (C.boundaryEndVertex small p))
            (C.restoreCorner inclusion q) x := by
  obtain ⟨n, c, at_first, at_last, covers⟩ := C.exists_boundary_link small p
  have start : C.linkMate small (C.boundaryEndVertex small p) c.first = c.first := by
    apply Subtype.ext
    change C.mateGerm small c.first.val = c.first.val
    rw [at_first]
    exact (C.mateGerm_eq_self_iff small p.val).mpr p.property
  have finish : C.linkMate small (C.boundaryEndVertex small p)
      (C.linkTurn small (C.boundaryEndVertex small p) c.last) =
        C.linkTurn small (C.boundaryEndVertex small p) c.last := by
    apply Subtype.ext
    change C.mateGerm small (C.linkTurn small (C.boundaryEndVertex small p) c.last).val = _
    rw [at_last]
    exact (C.mateGerm_eq_self_iff small (C.boundaryMate small p).val).mpr
      (C.boundaryMate small p).property
  have first' : C.IsBoundaryEdge large (C.germEdge c.first.val) := at_first.symm ▸ first
  have last' : C.IsBoundaryEdge large (C.germEdge (C.turnGerm c.last.val)) := by
    change C.IsBoundaryEdge large (C.germEdge (C.linkTurn small _ c.last).val)
    rw [at_last]
    exact last
  exact ⟨C.restoredBoundaryFanIsometry inclusion c covers start finish first' last',
    C.restoredBoundaryFanIsometry_faceMap inclusion c covers start finish first' last'⟩

end Unfoldings.TriangleComplex
