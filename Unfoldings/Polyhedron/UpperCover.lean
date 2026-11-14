module

public import Unfoldings.Polyhedron.UpperGraph
public import Unfoldings.Polyhedron.UpperTriangles
public import Unfoldings.Polyhedron.FaceNormalContact
public import Unfoldings.Geometry.SegmentEquation
public import Unfoldings.Geometry.TriangleFrontier

/-! Original upward triangles cover the full upper graph, including its silhouette. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.SupportingNormals

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (N : F.SupportingNormals)

def edgeEquation (fe : Face × Fin 3) : Plane →ᵃ[ℝ] ℝ :=
  segmentEquation (N.projectFace fe.1 ((C.triangle fe.1).vertex fe.2))
    (N.projectFace fe.1 ((C.triangle fe.1).vertex (Triangle.next fe.2)))

theorem edgeEquation_ne_zero (fe : Face × Fin 3) : N.edgeEquation fe ≠ 0 :=
  segmentEquation_ne_zero _ _

end Unfoldings.SpatialFolding.SupportingNormals

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

theorem upperPoint_in_original_face_of_regular {p : Plane} (member : p ∈ P.bodyFootprint)
    (regular : ∀ fe, N.edgeEquation fe p ≠ 0) :
    ∃ f : N.UpperFace, ∃ x : C.Cell f.val, F.place f.val x.val = P.upperPoint N p := by
  have boundary := P.upperPoint_mem_frontier N member
  rw [← P.boundary] at boundary
  obtain ⟨g, x, member_x, image⟩ := Set.mem_iUnion.mp boundary
  have inside : x ∈ interior (C.triangle g).carrier := by
    by_contra outside
    have boundary_x : x ∈ frontier (C.triangle g).carrier :=
      ⟨(C.triangle g).compact_carrier.isClosed.closure_eq.symm ▸ member_x, outside⟩
    obtain ⟨e, on_edge⟩ := Set.mem_iUnion.mp ((C.triangle g).frontier_eq_union_edges ▸ boundary_x)
    have projected : p ∈ segment ℝ
        (N.projectFace g ((C.triangle g).vertex e))
        (N.projectFace g ((C.triangle g).vertex (Triangle.next e))) := by
      rw [← image_segment ℝ (N.projectFace g)]
      exact ⟨x, on_edge, (congrArg Cap.horizontal image).trans (P.horizontal_upperPoint N p)⟩
    exact regular (g, e) (segmentEquation_eq_zero projected)
  obtain ⟨f, height⟩ := P.exists_upperHeight_eq N p
  have contact : inner ℝ (N.normal f.val) (F.place g x - F.place f.val 0) = 0 := by
    rw [image]
    apply (N.on_support_iff f _).mpr
    rw [P.horizontal_upperPoint, P.height_upperPoint]
    exact height
  have same_normal := P.normal_eq_of_interior_contact N f.val g inside contact
  have upward : 0 < N.normal g 2 := by rw [← same_normal]; exact f.property
  exact ⟨⟨g, upward⟩, ⟨x, member_x⟩, image⟩

/-- Every original upward triangle projects into the actual body's horizontal footprint. -/
theorem upperTriangle_subset_bodyFootprint (f : N.UpperFace) :
    (N.upperTriangle f).carrier ⊆ P.bodyFootprint := by
  intro p member
  obtain ⟨x, hx, equal⟩ := ((C.triangle f.val).affineImage_carrier _ _).subset member
  exact ⟨F.place f.val x, F.faceImage_subset_vertexHull f.val ⟨x, hx, rfl⟩, equal⟩

/-- No new projected triangles are needed at the silhouette. Closedness extends the
regular-point cover to the whole convex footprint, even when some faces are vertical. -/
theorem upperTriangles_cover_bodyFootprint :
    (⋃ f : N.UpperFace, (N.upperTriangle f).carrier) = P.bodyFootprint := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun f => P.upperTriangle_subset_bodyFootprint N f
  · let U := ⋃ f : N.UpperFace, (N.upperTriangle f).carrier
    have closed : IsClosed U :=
      (isCompact_iUnion (fun f : N.UpperFace => (N.upperTriangle f).compact_carrier)).isClosed
    have regular_covered : interior P.bodyFootprint ∩
        {p | ∀ fe, N.edgeEquation fe p ≠ 0} ⊆ U := by
      intro p hp
      obtain ⟨f, x, equal⟩ := P.upperPoint_in_original_face_of_regular N (interior_subset hp.1) hp.2
      apply Set.mem_iUnion.mpr
      refine ⟨f, ((C.triangle f.val).affineImage_carrier _ _).symm.subset ?_⟩
      exact ⟨x.val, x.property, (congrArg Cap.horizontal equal).trans (P.horizontal_upperPoint N p)⟩
    have dense := AffineArrangement.dense_regular N.edgeEquation N.edgeEquation_ne_zero
    have interior_covered : interior P.bodyFootprint ⊆ U :=
      (dense.open_subset_closure_inter isOpen_interior).trans
        (closure_minimal regular_covered closed)
    have regular_closed := (P.convex_bodyFootprint.closure_interior_eq_closure_of_nonempty_interior
      P.interior_bodyFootprint).trans P.compact_bodyFootprint.isClosed.closure_eq
    rw [← regular_closed]
    exact closure_minimal interior_covered closed

end Unfoldings.SpatialFolding.ConvexBoundary
