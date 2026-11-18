module

public import Unfoldings.Complex.SurvivingBoundaryTrace
public import Unfoldings.Polyhedron.ProjectedBoundaryChain

/-! Surviving untouched sides retain every original spatial and projected bank point. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {small large : Set C.Seam} (inclusion : small ⊆ large) {n : ℕ}
  (chain : (C.boundarySystem small).Chain n)
  (survives : ∀ i, C.IsBoundaryEdge large (C.germEdge (chain.point i).val))

/-- Equal original germs fix the physical endpoint independently of the retained cuts. -/
theorem boundaryPosition_eq_of_same_germ (p : C.BoundaryEnd small)
    (q : C.BoundaryEnd large) (same : p.val = q.val) :
    F.boundaryPosition p = F.boundaryPosition q :=
  (F.boundaryPosition_raw p).trans
    ((congrArg (fun g : C.Germ => F.place g.1.1 ((C.triangle g.1.1).vertex g.1.2)) same).trans
      (F.boundaryPosition_raw q).symm)

theorem survivingBoundaryEnd_position (p : C.BoundaryEnd small)
    (kept : C.IsBoundaryEdge large (C.germEdge p.val)) :
    F.boundaryPosition (C.survivingBoundaryEnd p kept) = F.boundaryPosition p :=
  F.boundaryPosition_eq_of_same_germ _ _ rfl

/-- The entire actual physical projected polygon, with both true endpoints, is identical. -/
theorem survivingBoundaryChain_projected :
    F.projectedBoundaryChain (C.survivingBoundaryChain inclusion chain survives) =
      F.projectedBoundaryChain chain := by
  let restored := C.survivingBoundaryChain inclusion chain survives
  have last_named : restored.last = C.survivingBoundaryEnd chain.last (survives (Fin.last n)) :=
    C.survivingBoundaryChain_point inclusion chain survives (Fin.last n)
  have final_germ : (C.boundaryTurn large restored.last).val =
      (C.boundaryTurn small chain.last).val :=
    (congrArg (fun p : C.BoundaryEnd large => (C.boundaryTurn large p).val) last_named).trans
      (C.survivingBoundaryEnd_turn_germ chain.last (survives (Fin.last n)))
  have final_position := F.boundaryPosition_eq_of_same_germ _ _ final_germ
  apply congrArg PolygonalChain.mk
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · exact (F.projectedBoundaryChain_vertex_last restored).trans
      ((congrArg Cap.horizontal final_position).trans
        (F.projectedBoundaryChain_vertex_last chain).symm)
  · have position := F.boundaryPosition_eq_of_same_germ (restored.point i) (chain.point i) rfl
    exact (F.projectedBoundaryChain_vertex_castSucc restored i).trans
      ((congrArg Cap.horizontal position).trans
        (F.projectedBoundaryChain_vertex_castSucc chain i).symm)

end Unfoldings.SpatialFolding
