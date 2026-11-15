module

public import Unfoldings.Boundary.Exact
public import Unfoldings.Complex.BoundaryQuotient
public import Unfoldings.Complex.Vertices

/-! A regular point detects whether its original triangle edge is an actual bank. -/

@[expose] public section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- At an edge interior the quotient bank boundary detects the very same original edge.
No manifold or planar development assumption is needed. -/
theorem isBoundaryEdge_of_regular_bankBoundary (retain : Set C.Seam) (edge : EdgeRef Face)
    (x : (C.triangle edge.face).Edge edge.edge)
    (regular : ¬ C.IsVertex (C.edgePoint edge x))
    (boundary : MetricGluing.point C.Cell (C.glue retain) (C.edgePoint edge x) ∈
      C.bankBoundary retain) : C.IsBoundaryEdge retain edge := by
  obtain ⟨bank, y, equal⟩ := Set.mem_iUnion.mp boundary
  have related := (C.point_eq_iff retain _ _).mp equal
  have other_regular : ¬ C.IsVertex (C.edgePoint bank.val y) :=
    fun vertex => regular ((C.eqvGen_preserves_vertex retain related).mp vertex)
  have tagged := (C.bankMap_eq_iff retain bank y other_regular (C.edgePoint edge x)).mp equal
  have same := C.onEdge_unique regular (C.edgePoint_onEdge edge x)
    (tagged ▸ C.edgePoint_onEdge bank.val y)
  exact same.symm ▸ bank.property

/-- One actual open-edge point is enough to test boundary status in either direction. -/
theorem isBoundaryEdge_iff_regular_bankBoundary (retain : Set C.Seam) (edge : EdgeRef Face)
    (x : (C.triangle edge.face).Edge edge.edge)
    (regular : ¬ C.IsVertex (C.edgePoint edge x)) :
    C.IsBoundaryEdge retain edge ↔
      MetricGluing.point C.Cell (C.glue retain) (C.edgePoint edge x) ∈ C.bankBoundary retain :=
  ⟨fun boundary => C.bankMap_mem_bankBoundary retain ⟨edge, boundary⟩ x,
    C.isBoundaryEdge_of_regular_bankBoundary retain edge x regular⟩

end Unfoldings.TriangleComplex
