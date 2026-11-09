module

public import Unfoldings.Boundary
public import Unfoldings.Complex.Exact

/-!
# Separation of boundary-bank interiors

The exact metric quotient keeps every nonvertex point of an unpaired edge
separate from all other tagged points. Distinct bank interiors therefore have
distinct metric images. Endpoints may still be joined by other retained seams.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

theorem not_crosses_of_boundary {retain : Set C.Seam} {e : EdgeRef Face} {a b : C.Total}
    (boundary : C.IsBoundaryEdge retain e) (regular : ¬ C.IsVertex a) (on_edge : C.OnEdge e a) :
    ¬ C.Crosses retain a b := by
  rintro ⟨s, hs, side, x, ha, hb⟩
  have edge_equal := C.onEdge_unique regular on_edge
    (ha ▸ C.edgePoint_onEdge (C.seamSide s side) x)
  apply boundary
  refine ⟨s, hs, ?_⟩
  cases side
  · exact Or.inl edge_equal
  · exact Or.inr edge_equal

/-- A nonvertex boundary point is never identified with another tagged point. -/
theorem point_eq_iff_of_boundary {retain : Set C.Seam} {e : EdgeRef Face} {a b : C.Total}
    (boundary : C.IsBoundaryEdge retain e) (regular : ¬ C.IsVertex a) (on_edge : C.OnEdge e a) :
    MetricGluing.point C.Cell (C.glue retain) a = MetricGluing.point C.Cell (C.glue retain) b ↔
      a = b := by
  rw [C.point_eq_iff, C.eqvGen_iff_of_regular retain regular]
  exact or_iff_left (C.not_crosses_of_boundary boundary regular on_edge)

/-- Canonical bank maps cannot identify distinct points when one lies in an edge interior. -/
theorem bankMap_eq_iff (retain : Set C.Seam) (bank : C.BoundaryBank retain)
    (x : (C.triangle bank.val.face).Edge bank.val.edge)
    (regular : ¬ C.IsVertex (C.edgePoint bank x))
    (b : C.Total) :
    C.bankMap retain bank x = MetricGluing.point C.Cell (C.glue retain) b ↔
      C.edgePoint bank x = b :=
  C.point_eq_iff_of_boundary bank.property regular (C.edgePoint_onEdge bank x)

/-- Different unpaired edges have disjoint images away from their corners. -/
theorem bankMap_ne_of_ne (retain : Set C.Seam) {bank bank' : C.BoundaryBank retain}
    (different : bank ≠ bank') (x : (C.triangle bank.val.face).Edge bank.val.edge)
    (y : (C.triangle bank'.val.face).Edge bank'.val.edge)
    (regular : ¬ C.IsVertex (C.edgePoint bank x)) :
    C.bankMap retain bank x ≠ C.bankMap retain bank' y := by
  intro equal
  have tagged := (C.bankMap_eq_iff retain bank x regular (C.edgePoint bank' y)).mp equal
  have same := C.onEdge_unique regular (C.edgePoint_onEdge bank x)
    (tagged ▸ C.edgePoint_onEdge bank' y)
  exact different (Subtype.ext same)

end Unfoldings.TriangleComplex
