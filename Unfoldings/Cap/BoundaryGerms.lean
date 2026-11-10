module

public import Unfoldings.Cap.Boundary
public import Unfoldings.Cap.GermSupports
public import Unfoldings.Geometry.BoundaryHalfplanes

/-! The actual first and last germs of a boundary link lie on the horizontal convex rim. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem projected_bank_subset_frontier (bank : C.BoundaryBank Set.univ) :
    K.projectFace bank.val.face '' (C.triangle bank.val.face).edge bank.val.edge ⊆
      frontier K.footprint := by
  rintro _ ⟨x, member, rfl⟩
  exact (K.projected_mem_frontier_iff_bankBoundary (C.bankMap Set.univ bank ⟨x, member⟩)).mpr
    (Set.mem_iUnion.mpr ⟨bank, ⟨⟨x, member⟩, rfl⟩⟩)

theorem boundary_germDirection_height (p : C.Germ)
    (boundary : C.IsBoundaryEdge Set.univ (C.germEdge p)) :
    K.folding.germDirection p 2 = 0 := by
  have endpoint (edge : EdgeRef Face) (h : C.IsBoundaryEdge Set.univ edge) (b : Bool) :
      K.folding.germDirection (C.germOfEndpoint edge b) 2 = 0 := by
    rw [SpatialFolding.germDirection, K.folding.germFarPoint_germOfEndpoint]
    rw [PiLp.sub_apply]
    have apex := congrArg (fun a : C.Total => K.folding.place a.1 a.2.val)
      (C.cornerPoint_germOfEndpoint edge b)
    change K.folding.place (C.germOfEndpoint edge b).1.1
      ((C.triangle (C.germOfEndpoint edge b).1.1).vertex (C.germOfEndpoint edge b).1.2) =
        K.folding.place edge.face ((C.triangle edge.face).endpoint edge.edge b).val at apex
    rw [apex]
    rw [K.rim_horizontal ⟨edge, h⟩, K.rim_horizontal ⟨edge, h⟩, sub_self]
  simpa only [C.germOfEndpoint_germEdge] using endpoint (C.germEdge p) boundary p.2

theorem boundary_germ_segment_frontier {v : C.Vertex Set.univ}
    (p : C.LinkGerm Set.univ v) (boundary : C.IsBoundaryEdge Set.univ (C.germEdge p.val)) :
    segment ℝ (K.projectedVertex v) (Cap.horizontal (K.folding.germFarPoint p.val)) ⊆
      frontier K.footprint := by
  have raw (edge : EdgeRef Face) (h : C.IsBoundaryEdge Set.univ edge) (b : Bool) :
      segment ℝ
        (K.projectFace edge.face ((C.triangle edge.face).endpoint edge.edge b).val)
        (Cap.horizontal (K.folding.germFarPoint (C.germOfEndpoint edge b))) ⊆
          frontier K.footprint := by
    rw [K.folding.germFarPoint_germOfEndpoint]
    have image := K.projected_bank_subset_frontier ⟨edge, h⟩
    change K.projectFace edge.face '' segment ℝ ((C.triangle edge.face).vertex edge.edge)
      ((C.triangle edge.face).vertex (Triangle.next edge.edge)) ⊆ _ at image
    rw [image_segment] at image
    cases b
    · exact image
    · change segment ℝ (K.projectFace edge.face ((C.triangle edge.face).vertex
        (Triangle.next edge.edge))) (K.projectFace edge.face
          ((C.triangle edge.face).vertex edge.edge)) ⊆ _
      rw [segment_symm]
      exact image
  have result := raw (C.germEdge p.val) boundary p.val.2
  rw [C.germOfEndpoint_germEdge] at result
  have apex := K.folding.linkGerm_apex Set.univ v p
  have endpoint : K.projectFace (C.germEdge p.val).face
      ((C.triangle (C.germEdge p.val).face).endpoint (C.germEdge p.val).edge p.val.2).val =
      K.projectedVertex v := by
    change Cap.horizontal (K.folding.place p.val.1.1
      ((C.triangle p.val.1.1).endpoint (C.germEdge p.val).edge p.val.2).val) = _
    have equal := congrArg (fun a : C.Total => Cap.horizontal (K.folding.place a.1 a.2.val))
      (C.cornerPoint_germOfEndpoint (C.germEdge p.val) p.val.2)
    rw [C.germOfEndpoint_germEdge] at equal
    exact equal.symm.trans (congrArg Cap.horizontal apex)
  rwa [endpoint] at result

end Unfoldings.ConvexCap
