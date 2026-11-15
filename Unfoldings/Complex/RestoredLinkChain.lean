module

public import Unfoldings.Complex.LinkSteps
public import Unfoldings.Complex.BoundaryLink

/-! Restoring seams preserves a complete boundary fan when its two terminal banks survive. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {small large : Set C.Seam} (inclusion : small ⊆ large)

/-- The same original germ in the vertex class obtained by restoring seams. -/
def restoreLinkGerm {w : C.Vertex small} (p : C.LinkGerm small w) :
    C.LinkGerm large (C.vertexForgetCuts inclusion w) :=
  ⟨p.val, congrArg (C.vertexForgetCuts inclusion) p.property⟩

theorem restoreLinkGerm_injective (w : C.Vertex small) :
    Function.Injective (C.restoreLinkGerm inclusion (w := w)) := by
  intro p q same
  exact Subtype.ext (congrArg
    (fun q : C.LinkGerm large (C.vertexForgetCuts inclusion w) => q.val) same)

/-- The original ordered corners and their original crossing seams are retained literally. -/
def restoreLinkChain {w : C.Vertex small} {n : ℕ}
    (c : (C.linkSystem small w).Chain n) :
    (C.linkSystem large (C.vertexForgetCuts inclusion w)).Chain n where
  point i := C.restoreLinkGerm inclusion (c.point i)
  injective := (C.restoreLinkGerm_injective inclusion w).comp c.injective
  disjoint i j same := c.disjoint i j (Subtype.ext (congrArg
    (fun q : C.LinkGerm large (C.vertexForgetCuts inclusion w) => q.val) same))
  next := by
    intro i
    obtain ⟨s, kept, side, b, first, last⟩ := C.chain_next_crosses small w c i
    apply Subtype.ext
    exact C.mateGerm_of_crossing ⟨s, inclusion kept, side, b, first, last⟩

/-- Once the two terminal banks are present, connectedness leaves no extra corners outside
this same original chain, even if other seams elsewhere are restored. -/
theorem restoreLinkChain_covers {w : C.Vertex small} {n : ℕ}
    (c : (C.linkSystem small w).Chain n)
    (first : C.IsBoundaryEdge large (C.germEdge c.first.val))
    (last : C.IsBoundaryEdge large (C.germEdge (C.turnGerm c.last.val))) :
    ∀ p, (C.restoreLinkChain inclusion c).Visited p := by
  apply (C.restoreLinkChain inclusion c).covers (C.linkSystem_connected large _)
  · exact Or.inr (Subtype.ext ((C.mateGerm_eq_self_iff large c.first.val).mpr first))
  · exact Or.inr (Subtype.ext
      ((C.mateGerm_eq_self_iff large (C.turnGerm c.last.val)).mpr last))

/-- Surviving terminal banks certify equality of the actual original corner sets.
This is stronger than equality of their total angles and does not assume a planar layout. -/
theorem boundary_fan_corners_iff (p : C.BoundaryEnd small)
    (first : C.IsBoundaryEdge large (C.germEdge p.val))
    (last : C.IsBoundaryEdge large (C.germEdge (C.boundaryMate small p).val))
    (a : C.Corner) :
    C.vertexOfCorner large a = C.vertexForgetCuts inclusion (C.boundaryEndVertex small p) ↔
      C.vertexOfCorner small a = C.boundaryEndVertex small p := by
  constructor
  · intro at_vertex
    obtain ⟨n, c, at_first, at_last, _covers⟩ := C.exists_boundary_link small p
    have first' : C.IsBoundaryEdge large (C.germEdge c.first.val) := at_first.symm ▸ first
    have last' : C.IsBoundaryEdge large (C.germEdge (C.turnGerm c.last.val)) := by
      change C.IsBoundaryEdge large (C.germEdge (C.linkTurn small _ c.last).val)
      rw [at_last]
      exact last
    let germ : C.LinkGerm large (C.vertexForgetCuts inclusion (C.boundaryEndVertex small p)) :=
      ⟨(a, false), at_vertex⟩
    obtain ⟨i, same | same⟩ := C.restoreLinkChain_covers inclusion c first' last' germ
    · have corners : a = (c.point i).val.1 :=
        congrArg (fun q : C.LinkGerm large _ => q.val.1) same
      rw [corners]
      exact (c.point i).property
    · have corners : a = (c.point i).val.1 :=
        congrArg (fun q : C.LinkGerm large _ => q.val.1) same
      rw [corners]
      exact (c.point i).property
  · exact congrArg (C.vertexForgetCuts inclusion)

/-- In particular the complete angle, including all original corner contributions, is unchanged. -/
theorem boundary_fan_totalAngle (p : C.BoundaryEnd small)
    (first : C.IsBoundaryEdge large (C.germEdge p.val))
    (last : C.IsBoundaryEdge large (C.germEdge (C.boundaryMate small p).val)) :
    C.totalAngle large (C.vertexForgetCuts inclusion (C.boundaryEndVertex small p)) =
      C.totalAngle small (C.boundaryEndVertex small p) := by
  classical
  simp only [totalAngle, C.boundary_fan_corners_iff inclusion p first last]

end Unfoldings.TriangleComplex
