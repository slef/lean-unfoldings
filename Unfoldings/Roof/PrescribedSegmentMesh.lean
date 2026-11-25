module

public import Unfoldings.Roof.SpatialEnvelopeInteriorSeams
public import Unfoldings.Roof.SpatialEnvelopeProjection
public import Unfoldings.Convex.PhysicalModelMesh
public import Unfoldings.Geometry.PrescribedSegments
public import Unfoldings.Geometry.PrescribedSubedge
public import Unfoldings.Geometry.SpatialEnvelopeOpenSeams
public import Unfoldings.Geometry.SegmentCoverForwardEdge
public import Unfoldings.Roof.VertexProgress
public import Unfoldings.Complex.SeamGraph

/-! Mesh a physical extension along any finite family of prescribed segments. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope.FiniteSlopeModel

variable {E : SlopeEnvelope} (M : E.FiniteSlopeModel)
  {J : Type} [Finite J] (extra : J → Plane →ᵃ[ℝ] ℝ) (proper : ∀ j, extra j ≠ 0)
  {n : ℕ} (first last : Fin n → Plane) (different : ∀ i, first i ≠ last i)
  {a : ℝ} (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ E.slopes)
  {Z : ℝ} {q : Plane} (inside : Z < -E.height q)

local notation "lines" => Sum.elim extra (segmentEquations first last different)

include proper in
theorem prescribedLines_ne_zero :
    ∀ k : J ⊕ (Fin n × Fin 3), lines k ≠ 0
  | .inl j => proper j
  | .inr k => segmentEquations_ne_zero first last different k

/-- Refine the spatial graph section along the supplied lines, segment carriers,
and endpoint lines. This construction does not use a routing potential. -/
def prescribedSegmentMesh : SpatialEnvelope.ConstrainedTriangulation M.plane lines Z :=
  M.mesh lines (prescribedLines_ne_zero extra proper first last different)
    positive inner_disk (q := q) inside

local notation "meshOfSegments" =>
  M.prescribedSegmentMesh extra proper first last different positive inner_disk inside

theorem prescribedSegmentMesh_conforming :
    TriangleFamily.Conforming (meshOfSegments).projectedTriangle :=
  M.mesh_conforming lines (prescribedLines_ne_zero extra proper first last different)
    positive inner_disk (q := q) inside

/-- Each prescribed segment is exactly a union of edges of the physical mesh,
including at every original bend and segment endpoint. -/
theorem prescribedSegmentMesh_edge_cover (i : Fin n)
    (start_inside : E.height (first i) ≤ -Z) (end_inside : E.height (last i) ≤ -Z) :
    let T := meshOfSegments
    segment ℝ (first i) (last i) =
      ⋃ e : {e : T.Index × Fin 3 // (T.projectedTriangle e.1).edge e.2 ⊆
          segment ℝ (first i) (last i)}, (T.projectedTriangle e.val.1).edge e.val.2 := by
  let T := meshOfSegments
  let aligned : SpatialEnvelope.ConstrainedTriangulation M.plane
      (segmentEquations first last different) Z := {
    toTriangulation := T.toTriangulation
    signs e k := T.signs e (.inr k)
    constrained e x present k := T.constrained e x present (.inr k) }
  apply aligned.prescribed_segment_eq_union_subedges <;>
    rw [M.clip_eq_sublevel] <;> assumption

/-- A whole fine edge in the cut carrier is contained in one prescribed
segment. The endpoint constraints keep it from straddling a coarse vertex. -/
theorem prescribedSegmentMesh_subedge (e : EdgeRef (meshOfSegments).Index)
    (selected : ((meshOfSegments).projectedTriangle e.face).edge e.edge ⊆
      ⋃ i, segment ℝ (first i) (last i)) :
    ∃ i, ((meshOfSegments).projectedTriangle e.face).edge e.edge ⊆
      segment ℝ (first i) (last i) := by
  let T := meshOfSegments
  obtain ⟨x, regular⟩ := (T.projectedTriangle e.face).exists_edge_nonvertex e.edge
  obtain ⟨i, on_segment⟩ := Set.mem_iUnion.mp (selected x.property)
  let U := triangleWithEdge (first i) (last i) (different i)
  exact ⟨i, U.edge_subset_of_signed_coords (T.projectedTriangle e.face)
    (fun k => T.signs e.face (.inr (i, k)))
    (fun k p hp => T.constrained e.face p hp (.inr (i, k))) 0 e.edge x regular on_segment⟩

variable (nonempty_section : (interior (SpatialEnvelope.clip M.plane Z)).Nonempty)

local instance prescribedSegmentMeshIndexFintype : Fintype (meshOfSegments).Index :=
  @Fintype.ofFinite _ (meshOfSegments).finite

local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation meshOfSegments)
  (M.prescribedSegmentMesh_conforming extra proper first last different positive inner_disk inside)
  nonempty_section

/-- At an interior mesh vertex, the fine seam in the same forward direction
can be chosen inside the remaining portion of the prescribed segment. -/
theorem prescribedSegmentMesh_forward_seam (i : Fin n)
    (start_inside : E.height (first i) ≤ -Z) (end_inside : E.height (last i) ≤ -Z)
    (v : (meshOfSegments).pairedComplex.Vertex Set.univ)
    (internal : ¬ (meshOfSegments).pairedComplex.IsBoundaryVertex Set.univ v)
    (on_path : (Q).projectedVertex v ∈ segment ℝ (first i) (last i))
    (not_last : (Q).projectedVertex v ≠ last i) :
    ∃ w s, (meshOfSegments).pairedComplex.seamGraph.IsLink s v w ∧
      (Q).projectedVertex w ∈ segment ℝ ((Q).projectedVertex v) (last i) ∧
      (Q).projectedVertex w ≠ (Q).projectedVertex v := by
  let T := meshOfSegments
  let D := T.pairedComplex
  let roof := Q
  have projected (j : T.Index) : roof.projectedTriangle j = T.projectedTriangle j :=
    T.toTriangulation.roof_projectedTriangle _ nonempty_section j
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
  have cover := (M.prescribedSegmentMesh_edge_cover extra proper first last different positive
    inner_disk inside i start_inside end_inside).subset
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

end Unfoldings.SlopeEnvelope.FiniteSlopeModel
