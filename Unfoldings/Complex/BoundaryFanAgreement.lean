module

public import Unfoldings.Complex.RestoredLinkChain

/-! The two named terminal bank germs determine an actual original corner fan. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {first last : Set C.Seam}

/-- A bank stays unpaired in the union exactly when it is unpaired in both original cuts. -/
theorem isBoundaryEdge_union_iff (edge : EdgeRef Face) :
    C.IsBoundaryEdge (first ∪ last) edge ↔
      C.IsBoundaryEdge first edge ∧ C.IsBoundaryEdge last edge := by
  classical
  simp only [IsBoundaryEdge, Set.mem_union, or_and_right, exists_or, not_or]

/-- Arbitrary cut descriptions need not be comparable. If both actual terminal germs agree,
they contain precisely the same original triangle corners at the named boundary copy. -/
theorem boundary_fan_corners_iff_of_terminal_germs (p : C.BoundaryEnd first)
    (q : C.BoundaryEnd last) (initial : p.val = q.val)
    (terminal : (C.boundaryMate first p).val = (C.boundaryMate last q).val) (a : C.Corner) :
    C.vertexOfCorner first a = C.boundaryEndVertex first p ↔
      C.vertexOfCorner last a = C.boundaryEndVertex last q := by
  have p_boundary : C.IsBoundaryEdge (first ∪ last) (C.germEdge p.val) :=
    (C.isBoundaryEdge_union_iff _).mpr ⟨p.property, initial.symm ▸ q.property⟩
  have p_mate : C.IsBoundaryEdge (first ∪ last)
      (C.germEdge (C.boundaryMate first p).val) :=
    (C.isBoundaryEdge_union_iff _).mpr
      ⟨(C.boundaryMate first p).property, terminal.symm ▸ (C.boundaryMate last q).property⟩
  have q_boundary : C.IsBoundaryEdge (first ∪ last) (C.germEdge q.val) := initial ▸ p_boundary
  have q_mate : C.IsBoundaryEdge (first ∪ last)
      (C.germEdge (C.boundaryMate last q).val) := terminal ▸ p_mate
  have first_copy := C.boundary_fan_corners_iff Set.subset_union_left p p_boundary p_mate a
  have last_copy := C.boundary_fan_corners_iff Set.subset_union_right q q_boundary q_mate a
  have same : C.vertexForgetCuts (Set.subset_union_left : first ⊆ first ∪ last)
        (C.boundaryEndVertex first p) =
      C.vertexForgetCuts (Set.subset_union_right : last ⊆ first ∪ last)
        (C.boundaryEndVertex last q) :=
    congrArg (fun germ : C.Germ => C.vertexOfCorner (first ∪ last) germ.1) initial
  rw [← first_copy, ← last_copy, same]

open Classical in
/-- Every original corner weight agrees, including intrinsic and projected angles. -/
theorem sum_boundary_fan_weights_eq_of_terminal_germs (p : C.BoundaryEnd first)
    (q : C.BoundaryEnd last) (initial : p.val = q.val)
    (terminal : (C.boundaryMate first p).val = (C.boundaryMate last q).val)
    (weight : C.Corner → ℝ) :
    (∑ a : C.Corner, if C.vertexOfCorner first a = C.boundaryEndVertex first p
      then weight a else 0) =
    ∑ a : C.Corner, if C.vertexOfCorner last a = C.boundaryEndVertex last q
      then weight a else 0 := by
  simp only [C.boundary_fan_corners_iff_of_terminal_germs p q initial terminal]

/-- Unreduced original fan angles agree without a planar development or overlap premise. -/
theorem totalAngle_eq_of_terminal_germs (p : C.BoundaryEnd first)
    (q : C.BoundaryEnd last) (initial : p.val = q.val)
    (terminal : (C.boundaryMate first p).val = (C.boundaryMate last q).val) :
    C.totalAngle first (C.boundaryEndVertex first p) =
      C.totalAngle last (C.boundaryEndVertex last q) :=
  C.sum_boundary_fan_weights_eq_of_terminal_germs p q initial terminal _

end Unfoldings.TriangleComplex
