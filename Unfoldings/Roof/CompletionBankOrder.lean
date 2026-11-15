module

public import Unfoldings.Roof.CompletionBankSubdivision
public import Unfoldings.Geometry.SegmentPartitionOrder
public import Unfoldings.Geometry.EdgeParameters
public import Unfoldings.Geometry.SharedEdgeInterior

/-! Physical fine edges on each original bank have a genuine endpoint-matched directed order. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionBankOrderIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- A regular fine boundary point belongs to just one fine boundary piece. -/
theorem faceSidePieces_regular_contact_unique (f : Face) (e : Fin 3)
    (a b : E.faceSidePieces f e) {p : Plane}
    (first : p ∈ (E.partition.projectedTriangle a.val.1.val).edge a.val.2)
    (last : p ∈ (E.partition.projectedTriangle b.val.1.val).edge b.val.2)
    (regular : ¬ (E.partition.projectedTriangle a.val.1.val).IsVertex p) : a = b := by
  have faces : a.val.1.val = b.val.1.val := by
    by_contra different
    rcases E.conforming a.val.1.val b.val.1.val different p
        ⟨(E.partition.projectedTriangle _).edge_subset _ first,
          (E.partition.projectedTriangle _).edge_subset _ last⟩ with vertices |
        ⟨k, l, shared, member⟩
    · exact regular vertices.1
    · have inside := (E.partition.projectedTriangle a.val.1.val).shared_edge_mem_interior_of_subsets
        (E.partition.projectedTriangle b.val.1.val) k l shared (E.partition.separated different)
        a.val.1.property b.val.1.property ⟨p, member⟩ regular
      exact (K.projectedTriangle f).not_mem_interior_of_mem_edge e (a.property first) inside
  have edges : a.val.2 = b.val.2 := by
    by_contra different
    exact regular ((E.partition.projectedTriangle a.val.1.val).isVertex_of_mem_edges different
      first (by simpa only [faces] using last))
  exact Subtype.ext (Prod.ext (Subtype.ext faces) edges)

open Classical in
/-- The physical open fine sides form a disjoint partition, rather than a cover with repetitions. -/
theorem faceSidePieces_open_disjoint (f : Face) (e : Fin 3) :
    Pairwise (fun a b : E.faceSidePieces f e => Disjoint
      (openSegment ℝ ((E.partition.projectedTriangle a.val.1.val).vertex a.val.2)
        ((E.partition.projectedTriangle a.val.1.val).vertex (Triangle.next a.val.2)))
      (openSegment ℝ ((E.partition.projectedTriangle b.val.1.val).vertex b.val.2)
        ((E.partition.projectedTriangle b.val.1.val).vertex (Triangle.next b.val.2)))) := by
  intro a b different
  apply Set.disjoint_left.mpr
  intro p first last
  apply different
  apply E.faceSidePieces_regular_contact_unique f e a b
    (openSegment_subset_segment ℝ _ _ first) (openSegment_subset_segment ℝ _ _ last)
  obtain ⟨t, bounds, rfl⟩ := (openSegment_eq_image_lineMap ℝ _ _).subset first
  exact (E.partition.projectedTriangle a.val.1.val).lineMap_edge_not_vertex a.val.2 bounds

open Classical in
/-- Each actual original side is an ordered chain of precisely its physical fine whole edges. -/
theorem exists_ordered_faceSidePieces (f : Face) (e : Fin 3) :
    Nonempty (OrderedSegmentPartition ((K.projectedTriangle f).vertex e)
      ((K.projectedTriangle f).vertex (Triangle.next e))
      (fun a : E.faceSidePieces f e => (E.partition.projectedTriangle a.val.1.val).vertex a.val.2)
      (fun a : E.faceSidePieces f e =>
        (E.partition.projectedTriangle a.val.1.val).vertex (Triangle.next a.val.2))) := by
  classical
  let first (a : E.faceSidePieces f e) :=
    (E.partition.projectedTriangle a.val.1.val).vertex a.val.2
  let last (a : E.faceSidePieces f e) :=
    (E.partition.projectedTriangle a.val.1.val).vertex (Triangle.next a.val.2)
  have genuine (a : E.faceSidePieces f e) : first a ≠ last a :=
    (E.partition.projectedTriangle a.val.1.val).edge_endpoints_ne a.val.2
  have inside (a : E.faceSidePieces f e) : segment ℝ (first a) (last a) ⊆
      (K.projectedTriangle f).edge e := a.property
  exact exists_ordered_segment_partition ((K.projectedTriangle f).edge_endpoints_ne e)
    first last genuine inside (E.faceSidePieces_open_disjoint f e)
      (E.faceSidePieces_cover f e).subset

end Unfoldings.ConvexRoof.CompletionMesh
