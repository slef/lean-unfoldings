module

public import Unfoldings.Polyhedron.UpperPlanes
public import Unfoldings.Geometry.TriangleAffine
public import Unfoldings.Geometry.ConformingTriangles
public import Unfoldings.Complex.SubdivisionInteriors
public import Unfoldings.Complex.Vertices

/-! Original upward triangles have conforming projections and exact geometric contacts. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.SupportingNormals

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (N : F.SupportingNormals)

def upperTriangle (f : N.UpperFace) : Triangle :=
  (C.triangle f.val).affineImage (N.projectFace f.val) (N.projectFace_injective f.val f.property)

def projectedEdge (e : EdgeRef Face) : Set Plane :=
  N.projectFace e.face '' (C.triangle e.face).edge e.edge

theorem upperTriangle_edge (f : N.UpperFace) (e : Fin 3) :
    (N.upperTriangle f).edge e = N.projectedEdge ⟨f.val, e⟩ :=
  (C.triangle f.val).affineImage_edge _ _ e

theorem projected_seam_edges_eq (s : C.Seam) :
    N.projectedEdge (C.left s) = N.projectedEdge (C.right s) := by
  apply Set.Subset.antisymm
  · rintro p ⟨x, hx, equal⟩
    let a : (C.triangle (C.left s).face).Edge (C.left s).edge := ⟨x, hx⟩
    exact ⟨(C.identify s a).val, (C.identify s a).property,
      (congrArg Cap.horizontal (F.joined s a)).symm.trans equal⟩
  · rintro p ⟨y, hy, equal⟩
    let b : (C.triangle (C.right s).face).Edge (C.right s).edge := ⟨y, hy⟩
    let a := (C.identify s).symm b
    refine ⟨a.val, a.property, ?_⟩
    have joined := congrArg Cap.horizontal (F.joined s a)
    have inverse := congrArg (fun w : (C.triangle (C.right s).face).Edge (C.right s).edge =>
      N.projectFace (C.right s).face w.val) ((C.identify s).apply_symm_apply b)
    exact joined.trans (inverse.trans equal)

theorem upper_points_equal (f g : N.UpperFace) (x : C.Cell f.val) (y : C.Cell g.val)
    (same : N.projectFace f.val x.val = N.projectFace g.val y.val) :
    F.place f.val x.val = F.place g.val y.val := by
  have first := (N.supporting_iff f (F.place g.val y.val)).mp
    (N.supporting f.val _ (F.faceImage_subset_vertexHull g.val ⟨y.val, y.property, rfl⟩))
  have last := (N.supporting_iff g (F.place f.val x.val)).mp
    (N.supporting g.val _ (F.faceImage_subset_vertexHull f.val ⟨x.val, x.property, rfl⟩))
  change F.place g.val y.val 2 ≤ N.supportHeight f.val (N.projectFace g.val y.val) at first
  change F.place f.val x.val 2 ≤ N.supportHeight g.val (N.projectFace f.val x.val) at last
  rw [← same, N.supportHeight_face] at first
  rw [same, N.supportHeight_face] at last
  ext i
  fin_cases i
  · exact congrArg (fun p : Plane => p 0) same
  · exact congrArg (fun p : Plane => p 1) same
  · exact le_antisymm last first

theorem upper_original_related (P : F.ConvexBoundary) (f g : N.UpperFace)
    (x : C.Cell f.val) (y : C.Cell g.val)
    (same : N.projectFace f.val x.val = N.projectFace g.val y.val) :
    Relation.EqvGen (C.glue Set.univ) ⟨f.val, x⟩ ⟨g.val, y⟩ := by
  apply (C.point_eq_iff Set.univ _ _).mp
  apply P.embedded
  exact N.upper_points_equal f g x y same

theorem projected_crossing_full_edge {a b : C.Total} (crossing : C.Crosses Set.univ a b) :
    ∃ e d : Fin 3, N.projectedEdge ⟨a.1, e⟩ = N.projectedEdge ⟨b.1, d⟩ ∧
      N.projectFace a.1 a.2.val ∈ N.projectedEdge ⟨a.1, e⟩ := by
  obtain ⟨s, _kept, side, x, rfl, rfl⟩ := crossing
  refine ⟨(C.seamSide s side).edge, (C.seamSide s (!side)).edge, ?_, ?_⟩
  · cases side
    · exact N.projected_seam_edges_eq s
    · exact (N.projected_seam_edges_eq s).symm
  · exact ⟨x.val, x.property, rfl⟩

theorem upperTriangles_conforming (P : F.ConvexBoundary) :
    TriangleFamily.Conforming N.upperTriangle := by
  intro f g different p member
  obtain ⟨x, hx, first⟩ := ((C.triangle f.val).affineImage_carrier _ _).subset member.1
  obtain ⟨y, hy, last⟩ := ((C.triangle g.val).affineImage_carrier _ _).subset member.2
  let a : C.Total := ⟨f.val, ⟨x, hx⟩⟩
  let b : C.Total := ⟨g.val, ⟨y, hy⟩⟩
  have related := N.upper_original_related P f g ⟨x, hx⟩ ⟨y, hy⟩ (first.trans last.symm)
  by_cases vertex : C.IsVertex a
  · obtain ⟨i, at_first⟩ := vertex
    obtain ⟨j, at_last⟩ := (C.eqvGen_preserves_vertex Set.univ related).mp ⟨i, at_first⟩
    refine Or.inl ⟨⟨i, ?_⟩, ⟨j, ?_⟩⟩
    · change N.projectFace f.val ((C.triangle f.val).vertex i) = p
      change (C.triangle f.val).vertex i = x at at_first
      exact (congrArg (N.projectFace f.val) at_first).trans first
    · change N.projectFace g.val ((C.triangle g.val).vertex j) = p
      change (C.triangle g.val).vertex j = y at at_last
      exact (congrArg (N.projectFace g.val) at_last).trans last
  · rcases (C.eqvGen_iff_of_regular Set.univ vertex).mp related with equal | crossing
    · exact (different (Subtype.ext (congrArg Sigma.fst equal))).elim
    · obtain ⟨e, d, shared, on_edge⟩ := N.projected_crossing_full_edge crossing
      refine Or.inr ⟨e, d, ?_, ?_⟩
      · rw [N.upperTriangle_edge, N.upperTriangle_edge]
        exact shared
      · rw [N.upperTriangle_edge]
        exact first ▸ on_edge

def projectFaceHomeomorph (f : N.UpperFace) : Plane ≃ₜ Plane :=
  { (N.projectFaceEquiv f).toEquiv with
    continuous_toFun := (N.projectFace f.val).continuous_of_finiteDimensional
    continuous_invFun := (N.projectFaceEquiv f).symm.toAffineMap.continuous_of_finiteDimensional }

theorem upperTriangles_nonoverlapping (P : F.ConvexBoundary) :
    Pairwise (fun f g : N.UpperFace =>
      Disjoint (interior (N.upperTriangle f).carrier) (interior (N.upperTriangle g).carrier)) := by
  intro f g different
  have carrier (f : N.UpperFace) : (N.upperTriangle f).carrier =
      N.projectFaceHomeomorph f '' (C.triangle f.val).carrier :=
    (C.triangle f.val).affineImage_carrier _ _
  rw [carrier f, carrier g, ← Homeomorph.image_interior, ← Homeomorph.image_interior]
  apply Set.disjoint_left.mpr
  rintro p ⟨x, hx, first⟩ ⟨y, hy, last⟩
  change N.projectFace f.val x = p at first
  change N.projectFace g.val y = p at last
  have related := N.upper_original_related P f g ⟨x, interior_subset hx⟩
    ⟨y, interior_subset hy⟩ (first.trans last.symm)
  have tags := C.eq_of_related_interior
    (a := ⟨f.val, ⟨x, interior_subset hx⟩⟩) (b := ⟨g.val, ⟨y, interior_subset hy⟩⟩) hx related
  exact different (Subtype.ext (congrArg Sigma.fst tags))

/-- Matching whole edges are actual original seams, not new geometric pairings. -/
theorem upper_exists_seam (P : F.ConvexBoundary) (f g : N.UpperFace) (different : f ≠ g)
    (e d : Fin 3) (same : (N.upperTriangle f).edge e = (N.upperTriangle g).edge d) :
    ∃ s : C.Seam, (C.left s = ⟨f.val, e⟩ ∧ C.right s = ⟨g.val, d⟩) ∨
      (C.left s = ⟨g.val, d⟩ ∧ C.right s = ⟨f.val, e⟩) := by
  let a : EdgeRef Face := ⟨f.val, e⟩
  let b : EdgeRef Face := ⟨g.val, d⟩
  obtain ⟨x, regular⟩ := (C.triangle f.val).exists_edge_nonvertex e
  have raw_regular : ¬ C.IsVertex (C.edgePoint a x) := regular
  have projected : N.projectFace f.val x.val ∈ (N.upperTriangle g).edge d := by
    rw [← same, N.upperTriangle_edge]
    exact ⟨x.val, x.property, rfl⟩
  rw [N.upperTriangle_edge] at projected
  obtain ⟨y, hy, point⟩ := projected
  let z : (C.triangle g.val).Edge d := ⟨y, hy⟩
  have related := N.upper_original_related P f g
    ((C.triangle f.val).edgeMap e x) ((C.triangle g.val).edgeMap d z) point.symm
  change Relation.EqvGen (C.glue Set.univ) (C.edgePoint a x) (C.edgePoint b z) at related
  rcases (C.eqvGen_iff_of_regular Set.univ raw_regular).mp related with equal | crossing
  · exact (different (Subtype.ext (congrArg Sigma.fst equal))).elim
  · have other : ¬ C.IsVertex (C.edgePoint b z) :=
      fun vertex => regular ((C.crosses_preserves_vertex crossing).mpr vertex)
    obtain ⟨s, _kept, side, w, first, last⟩ := crossing
    have first_edge : a = C.seamSide s side := C.onEdge_unique raw_regular
      (C.edgePoint_onEdge a x) (first.symm ▸ C.edgePoint_onEdge (C.seamSide s side) w)
    have last_edge : b = C.seamSide s (!side) := C.onEdge_unique other
      (C.edgePoint_onEdge b z)
      (last.symm ▸ C.edgePoint_onEdge (C.seamSide s (!side)) (C.across s side w))
    refine ⟨s, ?_⟩
    cases side
    · exact Or.inl ⟨first_edge.symm, last_edge.symm⟩
    · exact Or.inr ⟨last_edge.symm, first_edge.symm⟩

end Unfoldings.SpatialFolding.SupportingNormals
