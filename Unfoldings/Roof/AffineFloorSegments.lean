module

public import Unfoldings.Roof.AffineFloorRoof
public import Unfoldings.Geometry.PrescribedSegments
public import Unfoldings.Geometry.PrescribedSubedge
public import Unfoldings.Geometry.SegmentCoverForwardEdge
public import Unfoldings.Roof.VertexProgress
public import Unfoldings.Complex.SeamGraph
public import Unfoldings.Geometry.SegmentVertices
public import Unfoldings.Geometry.SpatialEnvelopeOpenSeams

/-! Prescribed cuts in an affine-floor section are exact unions of fine physical edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.FloorMesh

universe u

variable {I J : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {floor : Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  {extra : J → Plane →ᵃ[ℝ] ℝ}
  {A : Type u} (first last : A → Plane) (different : ∀ a, first a ≠ last a)
  (T : FloorMesh family floor (Sum.elim extra (segmentEquations first last different)) Z)

local instance floorSegmentIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- Reproduce each coarse segment as complete fine edges, including its endpoints. -/
theorem prescribed_edge_cover (a : A) (start_inside : first a ∈ clipAbove family floor Z)
    (end_inside : last a ∈ clipAbove family floor Z) :
    segment ℝ (first a) (last a) =
      ⋃ e : {e : T.Index × Fin 3 //
          (T.projectedTriangle e.1).edge e.2 ⊆ segment ℝ (first a) (last a)},
        (T.projectedTriangle e.val.1).edge e.val.2 := by
  let U := triangleWithEdge (first a) (last a) (different a)
  have cover : U.edge 0 ⊆ ⋃ i, (T.projectedTriangle i).carrier :=
    ((convex_clipAbove family floor Z).segment_subset start_inside end_inside).trans T.cover.subset
  exact TriangleFamily.edge_eq_union_subedges T.projectedTriangle U 0 cover
    (fun i k => T.sign i (.inr (a, k))) (fun i k p member => T.alignment i p member (.inr (a, k)))

/-- An entire fine edge in the carrier is contained in one prescribed segment. -/
theorem prescribed_subedge (e : EdgeRef T.Index)
    (covered : (T.projectedTriangle e.face).edge e.edge ⊆ ⋃ i, segment ℝ (first i) (last i)) :
    ∃ i, (T.projectedTriangle e.face).edge e.edge ⊆ segment ℝ (first i) (last i) := by
  obtain ⟨x, regular⟩ := (T.projectedTriangle e.face).exists_edge_nonvertex e.edge
  obtain ⟨i, on_segment⟩ := Set.mem_iUnion.mp (covered x.property)
  let U := triangleWithEdge (first i) (last i) (different i)
  exact ⟨i, U.edge_subset_of_signed_coords (T.projectedTriangle e.face)
    (fun k => T.sign e.face (.inr (i, k)))
    (fun k p hp => T.alignment e.face p hp (.inr (i, k))) 0 e.edge x regular on_segment⟩

variable (inside : (interior (clipAbove family floor Z)).Nonempty)

local notation "Q" => T.roof inside

/-- At an interior mesh vertex, the fine seam in the same forward direction
can be chosen inside the remaining portion of the prescribed segment. -/
theorem prescribed_forward_seam (i : A)
    (start_inside : first i ∈ clipAbove family floor Z)
    (end_inside : last i ∈ clipAbove family floor Z)
    (v : T.pairedComplex.Vertex Set.univ)
    (internal : ¬ T.pairedComplex.IsBoundaryVertex Set.univ v)
    (on_path : (Q).projectedVertex v ∈ segment ℝ (first i) (last i))
    (not_last : (Q).projectedVertex v ≠ last i) :
    ∃ w s, T.pairedComplex.seamGraph.IsLink s v w ∧
      (Q).projectedVertex w ∈ segment ℝ ((Q).projectedVertex v) (last i) ∧
      (Q).projectedVertex w ≠ (Q).projectedVertex v := by
  let D := T.pairedComplex
  let roof := Q
  have projected (j : T.Index) : roof.projectedTriangle j = T.projectedTriangle j :=
    T.roof_projectedTriangle inside j
  let I := {e : T.Index × Fin 3 // (T.projectedTriangle e.1).edge e.2 ⊆
    segment ℝ (first i) (last i)}
  let a (e : I) := (T.projectedTriangle e.val.1).vertex e.val.2
  let b (e : I) := (T.projectedTriangle e.val.1).vertex (Triangle.next e.val.2)
  have corner₀ (e : I) :
      roof.projectedVertex (D.vertexOfCorner Set.univ (e.val.1, e.val.2)) = a e := by
    rw [roof.projectedVertex_ofCorner, projected]
  have corner₁ (e : I) :
      roof.projectedVertex (D.vertexOfCorner Set.univ (e.val.1, Triangle.next e.val.2)) = b e := by
    rw [roof.projectedVertex_ofCorner, projected]
  have avoids (e : I) : roof.projectedVertex v ∉ openSegment ℝ (a e) (b e) := by
    intro in_open
    have in_face : roof.projectedVertex v ∈ (roof.projectedTriangle e.val.1).carrier := by
      rw [projected]
      exact (T.projectedTriangle e.val.1).edge_subset e.val.2
        ((openSegment_subset_segment ℝ _ _) in_open)
    obtain ⟨j, vertex⟩ := roof.projected_corner_of_vertex_mem v e.val.1 in_face
    rw [projected] at vertex
    exact (T.projectedTriangle e.val.1).not_isVertex_of_mem_openSegment e.val.2 in_open ⟨j, vertex⟩
  have cover := (T.prescribed_edge_cover first last different i start_inside end_inside).subset
  obtain ⟨e, forward | reverse⟩ := exists_forward_edge_of_finite_subsegment_cover a b (different i)
    cover (fun e => e.property (left_mem_segment ℝ _ _))
    (fun e => e.property (right_mem_segment ℝ _ _))
    (fun e => (T.projectedTriangle e.val.1).edge_endpoints_ne e.val.2)
    avoids on_path not_last
  · have at_v : D.vertexOfCorner Set.univ (e.val.1, e.val.2) = v :=
      roof.projectedVertex_injective ((corner₀ e).trans forward.1)
    obtain ⟨s, link⟩ := (D.exists_seamGraph_link_at_interior_corner e.val.1 e.val.2
      (at_v.symm ▸ internal)).1
    refine ⟨_, s, at_v ▸ link, ?_, ?_⟩
    · rw [corner₁ e]
      exact forward.2.1
    · rw [corner₁ e]
      exact forward.2.2
  · have at_v : D.vertexOfCorner Set.univ (e.val.1, Triangle.next e.val.2) = v :=
      roof.projectedVertex_injective ((corner₁ e).trans reverse.1)
    obtain ⟨s, link⟩ := (D.exists_seamGraph_link_at_interior_corner e.val.1
      (Triangle.next e.val.2) (at_v.symm ▸ internal)).2
    have next_next : Triangle.next (Triangle.next (Triangle.next e.val.2)) = e.val.2 := by
      generalize e.val.2 = j
      fin_cases j <;> decide
    rw [next_next] at link
    refine ⟨_, s, at_v ▸ link, ?_, ?_⟩
    · rw [corner₀ e]
      exact reverse.2.1
    · rw [corner₀ e]
      exact reverse.2.2

end Unfoldings.SpatialEnvelope.FloorMesh
