module

public import Unfoldings.Complex.RelativeCutGraph
public import Unfoldings.Complex.Neighborhood
public import Unfoldings.Complex.Folding

/-!
# Actual new cut arcs in the original surface

Their interiors avoid original banks and vertices. Distinct new cut seams have
disjoint open arcs, by the exact two-representative description of nonvertex
seam classes. These facts survive collapse of the original boundary.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {small large : Set C.Seam} (inclusion : small ⊆ large)

def relativeSeamMap (s : C.RelativeCutSeam small large) : C(unitInterval, C.Realization large) :=
  ⟨C.forgetCuts inclusion ∘ (C.boundaryGraph small).edge
      (C.relativeCutBank small large s false),
    (C.forgetCuts_lipschitz inclusion).continuous.comp
      ((C.boundaryGraph small).edge (C.relativeCutBank small large s false)).continuous⟩

theorem relativeSeamMap_zero (s : C.RelativeCutSeam small large) :
    C.relativeSeamMap inclusion s 0 =
      C.vertexPoint large (C.relativeCutVertex small large s false) := by
  change C.forgetCuts inclusion ((C.boundaryGraph small).edge _ 0) = _
  rw [(C.boundaryGraph small).edge_zero]
  exact (C.vertexPoint_vertexForgetCuts inclusion
    (C.vertexOfCorner small ((C.left s.val).face, (C.left s.val).edge))).symm

theorem relativeSeamMap_one (s : C.RelativeCutSeam small large) :
    C.relativeSeamMap inclusion s 1 =
      C.vertexPoint large (C.relativeCutVertex small large s true) := by
  change C.forgetCuts inclusion ((C.boundaryGraph small).edge _ 1) = _
  rw [(C.boundaryGraph small).edge_one]
  exact (C.vertexPoint_vertexForgetCuts inclusion
    (C.vertexOfCorner small ((C.left s.val).face, Triangle.next (C.left s.val).edge))).symm

theorem relativeSeamMap_avoids_vertices (s : C.RelativeCutSeam small large)
    (t : unitInterval) (positive : 0 < t) (less : t < 1) :
    C.relativeSeamMap inclusion s t ∉ Set.range (C.vertexPoint large) := by
  exact (C.mem_range_vertexPoint_iff large _).not.mpr
    (C.bankParameter_nonvertex small (C.relativeCutBank small large s false) t positive less)

theorem relativeSeamMap_avoids_boundary (s : C.RelativeCutSeam small large)
    (t : unitInterval) (positive : 0 < t) (less : t < 1) :
    C.relativeSeamMap inclusion s t ∉ C.bankBoundary large := by
  let x := C.bankParameter small (C.relativeCutBank small large s false) t
  have regular : ¬ C.IsVertex (C.edgePoint (C.left s.val) x) :=
    C.bankParameter_nonvertex small (C.relativeCutBank small large s false) t positive less
  have crossing : C.Crosses large (C.edgePoint (C.left s.val) x)
      (C.edgePoint (C.right s.val) (C.identify s.val x)) :=
    ⟨s.val, s.property.1, false, x, rfl, rfl⟩
  intro boundary
  obtain ⟨bank, y, equal⟩ := Set.mem_iUnion.mp boundary
  have related : Relation.EqvGen (C.glue large) (C.edgePoint (C.left s.val) x)
      (C.edgePoint bank.val y) := (C.point_eq_iff large _ _).mp equal.symm
  rcases (C.eqvGen_iff_eq_or_neighbor regular crossing).mp related with first | last
  · have edge := C.onEdge_unique regular (C.edgePoint_onEdge (C.left s.val) x)
      (first ▸ C.edgePoint_onEdge bank.val y)
    exact bank.property ⟨s.val, s.property.1, Or.inl edge.symm⟩
  · have other_regular : ¬ C.IsVertex (C.edgePoint (C.right s.val) (C.identify s.val x)) :=
      fun vertex => regular ((C.crosses_preserves_vertex crossing).mpr vertex)
    have edge := C.onEdge_unique other_regular
      (C.edgePoint_onEdge (C.right s.val) (C.identify s.val x))
      (last ▸ C.edgePoint_onEdge bank.val y)
    exact bank.property ⟨s.val, s.property.1, Or.inr edge.symm⟩

theorem relativeSeamMap_ne_of_ne {s r : C.RelativeCutSeam small large} (different : s ≠ r)
    (t z : unitInterval) (positive : 0 < t) (less : t < 1) :
    C.relativeSeamMap inclusion s t ≠ C.relativeSeamMap inclusion r z := by
  let x := C.bankParameter small (C.relativeCutBank small large s false) t
  let y := C.bankParameter small (C.relativeCutBank small large r false) z
  have regular : ¬ C.IsVertex (C.edgePoint (C.left s.val) x) :=
    C.bankParameter_nonvertex small (C.relativeCutBank small large s false) t positive less
  have crossing : C.Crosses large (C.edgePoint (C.left s.val) x)
      (C.edgePoint (C.right s.val) (C.identify s.val x)) :=
    ⟨s.val, s.property.1, false, x, rfl, rfl⟩
  intro equal
  have related : Relation.EqvGen (C.glue large) (C.edgePoint (C.left s.val) x)
      (C.edgePoint (C.left r.val) y) := (C.point_eq_iff large _ _).mp equal
  apply different
  apply Subtype.ext
  rcases (C.eqvGen_iff_eq_or_neighbor regular crossing).mp related with first | last
  · have edge := C.onEdge_unique regular (C.edgePoint_onEdge (C.left s.val) x)
      (first ▸ C.edgePoint_onEdge (C.left r.val) y)
    exact C.unique s.val r.val (Or.inl edge)
  · have other_regular : ¬ C.IsVertex (C.edgePoint (C.right s.val) (C.identify s.val x)) :=
      fun vertex => regular ((C.crosses_preserves_vertex crossing).mpr vertex)
    have edge := C.onEdge_unique other_regular
      (C.edgePoint_onEdge (C.right s.val) (C.identify s.val x))
      (last ▸ C.edgePoint_onEdge (C.left r.val) y)
    exact C.unique s.val r.val (Or.inr (Or.inr (Or.inl edge)))

theorem vertexPoint_mem_bankBoundary_iff (retain : Set C.Seam) (v : C.Vertex retain) :
    C.vertexPoint retain v ∈ C.bankBoundary retain ↔ C.IsBoundaryVertex retain v := by
  constructor
  · intro boundary
    obtain ⟨bank, y, equal⟩ := Set.mem_iUnion.mp boundary
    have vertex : (C.triangle bank.val.face).IsVertex y :=
      (C.mem_range_vertexPoint_iff retain _).mp ⟨v, equal.symm⟩
    obtain ⟨b, rfl⟩ := (C.triangle bank.val.face).exists_endpoint bank.val.edge y vertex
    cases b
    · refine ⟨bank.val, bank.property, Or.inl ?_⟩
      exact C.vertexPoint_injective retain equal.symm
    · refine ⟨bank.val, bank.property, Or.inr ?_⟩
      exact C.vertexPoint_injective retain equal.symm
  · exact fun boundary => C.vertexPoint_mem_bankBoundary retain ⟨v, boundary⟩

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

include F in
theorem relativeSeamMap_injective {small large : Set C.Seam} (inclusion : small ⊆ large)
    (s : C.RelativeCutSeam small large) : Function.Injective (C.relativeSeamMap inclusion s) := by
  intro t z equal
  have cell := (F.faceMap_isometry large (C.left s.val).face).injective equal
  have edge :=
    ((C.triangle (C.left s.val).face).edgeMap_isometry (C.left s.val).edge).injective cell
  exact C.bankParameter_injective small (C.relativeCutBank small large s false) edge

end Unfoldings.SpatialFolding
