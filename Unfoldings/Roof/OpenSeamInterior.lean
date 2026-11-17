module

public import Unfoldings.Roof.ProjectedOpening
public import Unfoldings.Geometry.HingePatch
public import Unfoldings.Geometry.SpatialEnvelopeOpenSeams

/-! Every actual open paired seam projects strictly inside the original convex roof footprint. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The two original incident faces provide a whole projected neighborhood at every
nonvertex seam point. This excludes the rim, independently of which seams are later cut. -/
theorem horizontal_openSeamImage_mem_interior (s : C.Seam) {z : Space}
    (on_open : z ∈ K.folding.openSeamImage s) :
    Cap.horizontal z ∈ interior K.footprint := by
  let T := K.projectedTriangle (C.left s).face
  let U := K.projectedTriangle (C.right s).face
  let e := (C.left s).edge
  let f := (C.right s).edge
  have projected : Cap.horizontal z ∈ openSegment ℝ (T.vertex e) (T.vertex (Triangle.next e)) :=
    (image_openSegment ℝ Cap.horizontal.toAffineMap _ _).subset ⟨z, on_open, rfl⟩
  have same := K.projected_seam_edges_eq s
  let H : HingePlacement T U e f (T.sharedEdgeIdentification U e f same) :=
    { place := AffineIsometryEquiv.refl ℝ Plane
      joined := fun _ => rfl
      opposite := K.projected_opposite s }
  obtain ⟨r, positive, cover⟩ := H.exists_ball_cover
    ⟨Cap.horizontal z, openSegment_subset_segment ℝ _ _ projected⟩
    (T.not_isVertex_of_mem_openSegment e projected)
  have included : Metric.ball (Cap.horizontal z) r ⊆ K.footprint := by
    intro p member
    have in_pair : p ∈ T.carrier ∪ U.carrier := by
      simpa only [H, AffineIsometryEquiv.coe_refl, Set.image_id] using cover member
    rw [K.footprint_eq_union_projectedTriangles]
    rcases in_pair with first | last
    · exact Set.mem_iUnion.mpr ⟨(C.left s).face, first⟩
    · exact Set.mem_iUnion.mpr ⟨(C.right s).face, last⟩
  exact mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨r, positive, included⟩)

end Unfoldings.ConvexRoof
