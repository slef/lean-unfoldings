module

public import Unfoldings.Cap.ConstrainedClipTriangles

/-! Original physical cuts are exact unions of actual whole edges in the extended roof clip. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem edge_image_eq_roofPoint_image (f : Face) (e : Fin 3) :
    K.folding.place f '' (C.triangle f).edge e =
      K.roofPoint '' (K.projectedTriangle f).edge e := by
  have projected_edge : (K.projectedTriangle f).edge e =
      K.projectFace f '' (C.triangle f).edge e :=
    (C.triangle f).affineImage_edge (K.projectFace f) (K.projectFace_injective f) e
  rw [projected_edge]
  ext z
  constructor
  · rintro ⟨x, member, rfl⟩
    exact ⟨K.projectFace f x, ⟨x, member, rfl⟩,
      K.roofPoint_projectFace f ⟨x, (C.triangle f).edge_subset e member⟩⟩
  · rintro ⟨_, ⟨x, member, rfl⟩, rfl⟩
    exact ⟨x, member, (K.roofPoint_projectFace f
      ⟨x, (C.triangle f).edge_subset e member⟩).symm⟩

namespace ClipSpatialTriangles

variable {K} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

/-- A physical fine edge is precisely the lift of its whole projected edge. -/
theorem edge_image_eq_roofPoint_image (i : T.Index) (e : Fin 3) :
    T.placement i '' (T.triangle i).edge e =
      K.roofPoint '' (T.projectedTriangle i).edge e := by
  ext z
  constructor
  · rintro ⟨x, member, rfl⟩
    refine ⟨K.projectFace (T.face i) x, (T.edgeProjection i e ⟨x, member⟩).property, ?_⟩
    exact (T.placement_eq_roofPoint i ((T.triangle i).edge_subset e member)).symm
  · rintro ⟨p, member, rfl⟩
    let x := (K.projectFaceEquiv (T.face i)).symm p
    have on_edge : x ∈ (T.triangle i).edge e := (T.triangle_edge i e).symm.subset
      ⟨p, member, rfl⟩
    refine ⟨x, on_edge, ?_⟩
    exact (T.placement_eq_roofPoint i ((T.triangle i).edge_subset e on_edge)).trans
      (congrArg K.roofPoint ((K.projectFaceEquiv (T.face i)).apply_symm_apply p))

end ClipSpatialTriangles

namespace LineAlignedClip

variable {K} {Z : ℝ} (L : K.LineAlignedClip Z K.originalEdgeEquations)

/-- Original spatial edges and original spatial cuts survive as exact whole-edge unions. -/
theorem original_spatial_edge_eq_union_subedges (lower : Z < 0) (f : Face) (e : Fin 3) :
    K.folding.place f '' (C.triangle f).edge e =
      ⋃ a : {a : L.partition.Index × Fin 3 //
          (L.partition.projectedTriangle a.1).edge a.2 ⊆ (K.projectedTriangle f).edge e},
        L.partition.placement a.val.1 '' (L.partition.triangle a.val.1).edge a.val.2 := by
  let E := {a : L.partition.Index × Fin 3 //
    (L.partition.projectedTriangle a.1).edge a.2 ⊆ (K.projectedTriangle f).edge e}
  calc
    K.folding.place f '' (C.triangle f).edge e =
        K.roofPoint '' (K.projectedTriangle f).edge e := K.edge_image_eq_roofPoint_image f e
    _ = K.roofPoint '' (⋃ a : E, (L.partition.projectedTriangle a.val.1).edge a.val.2) :=
      congrArg (fun S : Set Plane => K.roofPoint '' S) (L.original_edge_eq_union_subedges lower f e)
    _ = ⋃ a : E, K.roofPoint '' (L.partition.projectedTriangle a.val.1).edge a.val.2 :=
      Set.image_iUnion
    _ = ⋃ a : E, L.partition.placement a.val.1 ''
        (L.partition.triangle a.val.1).edge a.val.2 :=
      Set.iUnion_congr (fun a =>
        (L.partition.edge_image_eq_roofPoint_image a.val.1 a.val.2).symm)

end LineAlignedClip
end Unfoldings.ConvexCap
