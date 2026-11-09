module

public import Unfoldings.Polyhedron.EdgeExposure
public import Unfoldings.Complex.LinkOrdering

/-!
# The actual uncut convex triangulation has no unpaired banks

Finite closed face coverage and radial projection force another face at
every original edge point. At a nonvertex point, embeddedness and the exact
metric seam classes force a direct seam pairing. Thus every original edge
is paired and every original vertex link is cyclic, as derived conclusions.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem exists_other_face_at_edge (face : Face) (e : Fin 3)
    (x : (C.triangle face).Edge e) :
    ∃ g : Face, g ≠ face ∧ F.place face x.val ∈ F.faceImage g := by
  classical
  by_contra none
  let others : Set Space := ⋃ g : {g : Face // g ≠ face}, F.faceImage g.val
  have closed : IsClosed others := isClosed_iUnion_of_finite
    (fun g => (F.compact_faceImage g.val).isClosed)
  have outside : F.place face x.val ∉ others := by
    intro member
    obtain ⟨g, hg⟩ := Set.mem_iUnion.mp member
    exact none ⟨g.val, g.property, hg⟩
  obtain ⟨ε, positive, clear⟩ := Metric.isOpen_iff.mp closed.isOpen_compl _ outside
  obtain ⟨z, surface, near, not_face⟩ := P.exists_surface_near_edge_outside_face face e x ε positive
  have not_other : z ∉ others := clear (Metric.mem_ball.mpr near)
  obtain ⟨g, hg⟩ := Set.mem_iUnion.mp surface
  by_cases same : g = face
  · exact not_face (same ▸ hg)
  · exact not_other (Set.mem_iUnion.mpr ⟨⟨g, same⟩, hg⟩)

theorem exists_seam_at_edge (e : EdgeRef Face) : ∃ s : C.Seam, ∃ side : Bool,
    C.seamSide s side = e := by
  obtain ⟨x, regular⟩ := (C.triangle e.face).exists_edge_nonvertex e.edge
  obtain ⟨g, different, y, hy, image⟩ := P.exists_other_face_at_edge e.face e.edge x
  let a : C.Total := C.edgePoint e x
  let b : C.Total := ⟨g, ⟨y, hy⟩⟩
  have related := F.isEmbedded_iff.mp P.embedded a b image.symm
  have nonvertex : ¬ C.IsVertex a := regular
  rcases (C.eqvGen_iff_of_regular Set.univ nonvertex).mp related with same | crossing
  · have faces : e.face = g := congrArg Sigma.fst same
    exact (different faces.symm).elim
  · obtain ⟨s, _kept, side, p, source, _target⟩ := crossing
    have edges := C.onEdge_unique nonvertex (C.edgePoint_onEdge e x)
      (source ▸ C.edgePoint_onEdge (C.seamSide s side) p)
    exact ⟨s, side, edges.symm⟩

theorem not_isBoundaryEdge (e : EdgeRef Face) : ¬ C.IsBoundaryEdge Set.univ e := by
  intro boundary
  obtain ⟨s, side, equal⟩ := P.exists_seam_at_edge e
  apply boundary
  refine ⟨s, Set.mem_univ _, ?_⟩
  cases side
  · exact Or.inl equal.symm
  · exact Or.inr equal.symm

theorem not_isBoundaryVertex (v : C.Vertex Set.univ) : ¬ C.IsBoundaryVertex Set.univ v := by
  rintro ⟨e, boundary, _endpoint⟩
  exact P.not_isBoundaryEdge e boundary

theorem exists_cyclic_link (v : C.Vertex Set.univ) :
    ∃ n, ∃ c : (C.linkSystem Set.univ v).Chain n,
      C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first ∧ ∀ p, c.Visited p :=
  C.exists_cyclic_link Set.univ v (P.not_isBoundaryVertex v)

end Unfoldings.SpatialFolding.ConvexBoundary
