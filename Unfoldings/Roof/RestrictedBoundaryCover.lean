module

public import Unfoldings.Roof.RestrictedBoundaryExistence
public import Unfoldings.Roof.VertexProgress
public import Unfoldings.Roof.ProjectedConformity
public import Unfoldings.Complex.FaceRestrictionVertices
public import Unfoldings.Complex.BoundaryQuotient
public import Unfoldings.Metric.BankHalfPlaneFrames
public import Unfoldings.Polyhedron.BoundaryDirections

/-! Every nonempty whole-face roof restriction has an actual unpaired bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open MetricGluing

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
/-- A nonvertex frontier point of a whole-face restriction lies on an unpaired original edge. -/
theorem exists_restricted_bank_at_regular_frontier (U : Set Face) {p : Plane}
    (boundary : p ∈ frontier (K.restrictedCarrier U))
    (regular : ∀ f i, p ≠ (K.projectedTriangle f).vertex i) :
    ∃ bank : (C.restrictFaces U).BoundaryBank Set.univ,
      p ∈ (K.projectedTriangle bank.val.face.val).edge bank.val.edge := by
  let R := C.restrictFaces U
  have member := (K.compact_restrictedCarrier U).isClosed.frontier_subset boundary
  obtain ⟨f, in_face⟩ := Set.mem_iUnion.mp member
  have not_interior : p ∉ interior (K.projectedTriangle f.val).carrier := by
    intro inside
    exact boundary.2
      (interior_mono (Set.subset_iUnion (fun f : {f : Face // f ∈ U} =>
        (K.projectedTriangle f.val).carrier) f) inside)
  obtain ⟨e, on_edge⟩ := (K.projectedTriangle f.val).exists_edge_of_not_mem_interior
    ⟨p, in_face⟩ not_interior
  by_cases bank : R.IsBoundaryEdge Set.univ ⟨f, e⟩
  · exact ⟨⟨⟨f, e⟩, bank⟩, on_edge⟩
  · obtain ⟨s, _, left | right⟩ := not_not.mp bank
    all_goals
      have same : (K.projectedTriangle (R.left s).face.val).edge (R.left s).edge =
          (K.projectedTriangle (R.right s).face.val).edge (R.right s).edge :=
        K.projected_seam_edges_eq s.val
      have first : p ∈ (K.projectedTriangle (R.left s).face.val).edge (R.left s).edge := by
        first
        | simpa only [← left] using on_edge
        | rw [same]; simpa only [← right] using on_edge
      let T := K.projectedTriangle (R.left s).face.val
      let V := K.projectedTriangle (R.right s).face.val
      let H : HingePlacement T V (R.left s).edge (R.right s).edge
          (T.sharedEdgeIdentification V (R.left s).edge (R.right s).edge same) :=
        { place := AffineIsometryEquiv.refl ℝ Plane
          joined := fun _ => rfl
          opposite := K.projected_opposite s.val }
      have not_vertex : ¬ T.IsVertex p := by
        rintro ⟨i, same⟩
        exact regular (R.left s).face.val i same.symm
      obtain ⟨r, positive, cover⟩ := H.exists_ball_cover ⟨p, first⟩ not_vertex
      have included : Metric.ball p r ⊆ K.restrictedCarrier U := by
        intro q hq
        have in_pair : q ∈ T.carrier ∪ V.carrier := by
          simpa only [H, AffineIsometryEquiv.coe_refl, Set.image_id] using cover hq
        rcases in_pair with a | b
        · exact Set.mem_iUnion.mpr ⟨(R.left s).face, a⟩
        · exact Set.mem_iUnion.mpr ⟨(R.right s).face, b⟩
      exact (boundary.2 (mem_interior_iff_mem_nhds.mpr
        (Metric.mem_nhds_iff.mpr ⟨r, positive, included⟩))).elim

/-- A vertex on a conforming edge is one of its endpoints, even if named by a different face. -/
theorem projectedVertex_mem_edge_endpoints (v : C.Vertex Set.univ) (f : Face) (e : Fin 3)
    (member : K.projectedVertex v ∈ (K.projectedTriangle f).edge e) :
    K.projectedVertex v = (K.projectedTriangle f).vertex e ∨
      K.projectedVertex v = (K.projectedTriangle f).vertex (Triangle.next e) := by
  obtain ⟨⟨g, i⟩, rfl⟩ := C.vertexOfCorner_surjective Set.univ v
  simp only [K.projectedVertex_ofCorner] at member ⊢
  let A := K.projectedTriangle f
  let B := K.projectedTriangle g
  let p := B.vertex i
  change p ∈ A.edge e at member
  change p = A.vertex e ∨ p = A.vertex (Triangle.next e)
  by_cases same : g = f
  · subst g
    exact (A.edge_vertex_iff e ⟨p, member⟩).mp ⟨i, rfl⟩
  rcases K.projectedTriangles_conforming f g (Ne.symm same) p
    ⟨A.edge_subset e member, B.vertex_mem i⟩ with vertices | ⟨d, j, edge_eq, shared⟩
  · exact (A.edge_vertex_iff e ⟨p, member⟩).mp vertices.1
  · have p_on_B : p ∈ B.edge j := edge_eq ▸ shared
    have endpoint := (B.edge_vertex_iff j ⟨p, p_on_B⟩).mp ⟨i, rfl⟩
    let E : B.Edge j ≃ᵢ A.Edge d :=
      setIsometryEquiv (IsometryEquiv.refl Plane) _ _ (by
        change ∀ x : Plane, x ∈ A.edge d ↔ x ∈ B.edge j
        exact fun _ => Set.ext_iff.mp edge_eq _)
    have mapped := segment_isometry_maps_endpoint E ⟨p, p_on_B⟩ endpoint
    have vertex : A.IsVertex p := by
      have same_point : (E ⟨p, p_on_B⟩).val = p := rfl
      exact (A.edge_vertex_iff d ⟨p, shared⟩).mpr
        (mapped.imp (same_point.symm.trans ·) (same_point.symm.trans ·))
    exact (A.edge_vertex_iff e ⟨p, member⟩).mp vertex

open Classical in
/-- A fine vertex approached along regular frontier points has a literal boundary end of the
restricted complex at that very geometric point. -/
theorem exists_restricted_boundaryEnd_of_frontier_limit (U : Set Face)
    (v : C.Vertex Set.univ)
    (limit : K.projectedVertex v ∈ closure (frontier (K.restrictedCarrier U) \
      Set.range (fun i : Face × Fin 3 => (K.projectedTriangle i.1).vertex i.2))) :
    ∃ p : (C.restrictFaces U).BoundaryEnd Set.univ,
      C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ p) = v := by
  let R := C.restrictFaces U
  letI : Finite (R.BoundaryBank Set.univ) := R.finite_boundaryBank Set.univ
  let bankCarrier (b : R.BoundaryBank Set.univ) :=
    (K.projectedTriangle b.val.face.val).edge b.val.edge
  have closed : IsClosed (⋃ b, bankCarrier b) := by
    apply isClosed_iUnion_of_finite
    intro b
    exact ((K.projectedTriangle b.val.face.val).compact_edge b.val.edge).isClosed
  have cover : frontier (K.restrictedCarrier U) \
      Set.range (fun i : Face × Fin 3 => (K.projectedTriangle i.1).vertex i.2) ⊆ ⋃ b, bankCarrier b := by
    intro z hz
    obtain ⟨b, member⟩ := K.exists_restricted_bank_at_regular_frontier U hz.1
      (fun f i eq => hz.2 ⟨(f, i), eq.symm⟩)
    exact Set.mem_iUnion.mpr ⟨b, member⟩
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (closure_minimal cover closed limit)
  obtain start | finish := K.projectedVertex_mem_edge_endpoints v b.val.face.val b.val.edge hb
  · let p := (R.boundaryEndEquiv Set.univ).symm (b, false)
    refine ⟨p, K.projectedVertex_injective ?_⟩
    change K.projectedVertex (C.vertexOfCorner Set.univ (b.val.face.val, b.val.edge)) = _
    rw [K.projectedVertex_ofCorner]
    exact start.symm
  · let p := (R.boundaryEndEquiv Set.univ).symm (b, true)
    refine ⟨p, K.projectedVertex_injective ?_⟩
    change K.projectedVertex (C.vertexOfCorner Set.univ (b.val.face.val, Triangle.next b.val.edge)) = _
    rw [K.projectedVertex_ofCorner]
    exact finish.symm

end Unfoldings.ConvexRoof
