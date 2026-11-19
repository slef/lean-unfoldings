module

public import Unfoldings.Complex.ContourParentBanks
public import Unfoldings.Complex.DirectedBoundaryPath

/-! Original oriented parent-bank labels are separated at strict edge interiors. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)

/-- The actual directed parent-bank tag retains its child vertex and its cut side. -/
theorem contourParentBank_injective : Function.Injective
    (fun p : {v : C.Vertex Set.univ // v ∉ P.roots} × Bool =>
      C.contourParentBank S Q roots starts p.1.val p.1.property p.2) := by
  rintro ⟨vertex, side⟩ ⟨other, other_side⟩ equal
  have first := C.contourParentBank_start S Q roots starts vertex.val vertex.property side
  have last := C.contourParentBank_start S Q roots starts other.val other.property other_side
  have vertex_eq : vertex = other := Subtype.ext
    (first.symm.trans ((congrArg (fun p => C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ p)) equal).trans last))
  subst other
  apply congrArg (fun b : Bool => (vertex, b))
  cases side <;> cases other_side
  · rfl
  · exact (C.contourParentBank_distinct S Q roots starts vertex.val vertex.property equal).elim
  · exact (C.contourParentBank_distinct S Q roots starts vertex.val vertex.property equal.symm).elim
  · rfl

/-- Forgetting the endpoint orientation still preserves the original child and side.
The opposite orientation would produce a two-cycle in the ascending parent forest. -/
theorem contourParentBank_bank_injective : Function.Injective
    (fun p : {v : C.Vertex Set.univ // v ∉ P.roots} × Bool =>
      (C.boundaryEndEquiv (C.selectedRetain S)
        (C.contourParentBank S Q roots starts p.1.val p.1.property p.2)).1) := by
  intro p q equal
  rcases (C.boundaryEnd_bank_eq_iff (C.selectedRetain S) _ _).mp equal with same | reversed
  · exact C.contourParentBank_injective S Q roots starts same
  · have first := C.contourParentBank_start S Q roots starts p.1.val p.1.property p.2
    have last := C.contourParentBank_finish S Q roots starts q.1.val q.1.property q.2
    have child_parent : p.1.val = P.parent q.1.val := first.symm.trans
      ((congrArg (fun b => C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex _ b)) reversed).trans last)
    have first_end := C.contourParentBank_finish S Q roots starts p.1.val p.1.property p.2
    have last_start := C.contourParentBank_start S Q roots starts q.1.val q.1.property q.2
    have parent_child : P.parent p.1.val = q.1.val := by
      have turned := congrArg (C.boundaryTurn (C.selectedRetain S)) reversed
      rw [C.boundaryTurn_involutive] at turned
      exact first_end.symm.trans ((congrArg (fun b => C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex _ b)) turned).trans last_start)
    have left := P.ascending p.1.val p.1.property
    have right := P.ascending q.1.val q.1.property
    rw [parent_child] at left
    rw [← child_parent] at right
    exact (lt_asymm left right).elim

/-- Equality with a strict actual parent-bank point fixes the original child and cut side.
The other parameter is allowed to be a closed endpoint. -/
theorem contourParentBank_eq_of_path_eq
    (vertex other : {v : C.Vertex Set.univ // v ∉ P.roots}) (side other_side : Bool)
    (t s : unitInterval) (bounds : 0 < t ∧ t < 1)
    (equal : C.directedBoundaryPath
        (C.contourParentBank S Q roots starts other.val other.property other_side) s =
      C.directedBoundaryPath
        (C.contourParentBank S Q roots starts vertex.val vertex.property side) t) :
    (other, other_side) = (vertex, side) := by
  apply C.contourParentBank_bank_injective S Q roots starts
  by_contra different
  let p := C.contourParentBank S Q roots starts vertex.val vertex.property side
  let q := C.contourParentBank S Q roots starts other.val other.property other_side
  exact C.bankMap_ne_of_ne (C.selectedRetain S) (Ne.symm different)
    (C.bankParameterFromEnd (C.boundaryEndEquiv _ p).1 (C.boundaryEndEquiv _ p).2 t)
    (C.bankParameterFromEnd (C.boundaryEndEquiv _ q).1 (C.boundaryEndEquiv _ q).2 s)
    (C.bankParameterFromEnd_nonvertex _ _ t bounds.1 bounds.2) equal.symm

/-- A directed bank path retains its parameter when one point is strictly interior. -/
theorem directedBoundaryPath_parameter_eq_of_interior {retain : Set C.Seam}
    (p : C.BoundaryEnd retain) (s t : unitInterval) (bounds : 0 < t ∧ t < 1)
    (equal : C.directedBoundaryPath p s = C.directedBoundaryPath p t) : s = t := by
  let bank := (C.boundaryEndEquiv retain p).1
  let side := (C.boundaryEndEquiv retain p).2
  have tagged := (C.bankMap_eq_iff retain bank (C.bankParameterFromEnd bank side t)
    (C.bankParameterFromEnd_nonvertex bank side t bounds.1 bounds.2)
    (C.edgePoint bank (C.bankParameterFromEnd bank side s))).mp equal.symm
  have endpoints : ((C.triangle bank.val.face).endpoint bank.val.edge side).val ≠
      ((C.triangle bank.val.face).endpoint bank.val.edge (!side)).val := by
    cases side
    · exact (C.triangle bank.val.face).edge_endpoints_ne bank.val.edge
    · exact ((C.triangle bank.val.face).edge_endpoints_ne bank.val.edge).symm
  have position := congrArg (fun a : C.Total => a.2.val) tagged
  apply Subtype.ext
  exact ((AffineMap.lineMap_injective ℝ endpoints) position).symm

/-- At an actual strict parent-bank point, all three original labels are unique. -/
theorem contourParentBank_parameters_eq_of_path_eq
    (vertex other : {v : C.Vertex Set.univ // v ∉ P.roots}) (side other_side : Bool)
    (t s : unitInterval) (bounds : 0 < t ∧ t < 1)
    (equal : C.directedBoundaryPath
        (C.contourParentBank S Q roots starts other.val other.property other_side) s =
      C.directedBoundaryPath
        (C.contourParentBank S Q roots starts vertex.val vertex.property side) t) :
    (other, other_side, s) = (vertex, side, t) := by
  have named := Prod.mk.inj (C.contourParentBank_eq_of_path_eq S Q roots starts
    vertex other side other_side t s bounds equal)
  obtain ⟨rfl, rfl⟩ := named
  have parameter := C.directedBoundaryPath_parameter_eq_of_interior _ s t bounds equal
  subst s
  rfl

end Unfoldings.TriangleComplex
