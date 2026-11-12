module

public import Unfoldings.Complex.ParentBankEndpoints
public import Unfoldings.Complex.Folding

/-! Restored seam endpoints agree intrinsically, independently of the planar development. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

include F in
/-- Matching original endpoints on opposite banks become the same intrinsic vertex
as soon as their seam is restored. -/
theorem boundary_end_forgetCuts_eq_of_restored_seam
    {small large : Set C.Seam} (inclusion : small ⊆ large)
    (s : C.RelativeCutSeam small Set.univ) (kept : s.val ∈ large)
    (p q : C.BoundaryEnd small) (side : Bool)
    (first : (C.boundaryEndEquiv small p).1 =
      C.relativeCutBank small Set.univ s side)
    (last : (C.boundaryEndEquiv small q).1 =
      C.relativeCutBank small Set.univ s (!side))
    (same : C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex small p) =
      C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex small q)) :
    C.vertexForgetCuts inclusion (C.boundaryEndVertex small p) =
      C.vertexForgetCuts inclusion (C.boundaryEndVertex small q) := by
  have first_edge : C.germEdge p.val = C.seamSide s.val side :=
    congrArg Subtype.val first
  have last_edge : C.germEdge q.val = C.seamSide s.val (!side) :=
    congrArg Subtype.val last
  have first_germ : p.val = C.germOfEndpoint (C.seamSide s.val side) p.val.2 := by
    rw [← first_edge]
    exact (C.germOfEndpoint_germEdge p.val).symm
  have last_germ : q.val = C.germOfEndpoint (C.seamSide s.val (!side)) q.val.2 := by
    rw [← last_edge]
    exact (C.germOfEndpoint_germEdge q.val).symm
  let r := C.germOfEndpoint (C.seamSide s.val (!side))
    (C.acrossEndpoint s.val side p.val.2)
  have crossing : C.GermCrosses large p.val r :=
    ⟨s.val, kept, side, p.val.2, first_germ, rfl⟩
  have original : C.GermCrosses Set.univ p.val r :=
    ⟨s.val, Set.mem_univ _, side, p.val.2, first_germ, rfl⟩
  have same_face : r.1.1 = q.val.1.1 := by
    rw [last_germ]
    rfl
  have original_points : C.vertexPoint Set.univ (C.vertexOfCorner Set.univ r.1) =
      C.vertexPoint Set.univ (C.vertexOfCorner Set.univ q.val.1) := by
    rw [← original.vertex_eq]
    exact congrArg (C.vertexPoint Set.univ) same
  have same_cell (f g : Face) (x : C.Cell f) (y : C.Cell g) (faces : f = g)
      (equal : C.faceMap Set.univ f x = C.faceMap Set.univ g y) :
      (⟨f, x⟩ : C.Total) = ⟨g, y⟩ := by
    subst g
    exact congrArg (Sigma.mk f) ((F.faceMap_isometry Set.univ f).injective equal)
  have cells : C.cornerPoint r.1 = C.cornerPoint q.val.1 :=
    same_cell _ _ _ _ same_face original_points
  have vertices : C.vertexOfCorner large r.1 = C.vertexOfCorner large q.val.1 := by
    apply C.vertexPoint_injective large
    change MetricGluing.point C.Cell (C.glue large) (C.cornerPoint r.1) =
      MetricGluing.point C.Cell (C.glue large) (C.cornerPoint q.val.1)
    rw [cells]
  exact crossing.vertex_eq.trans vertices

end Unfoldings.SpatialFolding
