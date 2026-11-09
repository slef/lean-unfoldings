module

public import Unfoldings.Polyhedron.VertexHinge
public import Unfoldings.Cone.SpatialRange
public import Unfoldings.Geometry.FunctionalHomothety

/-!
# The whole actual tangent image is the constructed spatial support hinge

The spatial tangent fan and the original surface agree near the vertex.
Both the fan image and the constructed support hinge are positively radially
homogeneous, so their local equality extends to the whole affine cone.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.SpatialFolding.VertexHinge

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} {v : C.Vertex Set.univ} (H : F.VertexHinge v)

def carrier : Set Space :=
  {z | H.leftFunctional z = H.leftLevel ∧ H.rightFunctional z ≤ H.rightLevel} ∪
    {z | H.rightFunctional z = H.rightLevel ∧ H.leftFunctional z ≤ H.leftLevel}

theorem carrier_lineMap_iff (z : Space) {t : ℝ} (positive : 0 < t) :
    AffineMap.lineMap (F.toSpace Set.univ (C.vertexPoint Set.univ v)) z t ∈ H.carrier ↔
      z ∈ H.carrier := by
  simp only [carrier, Set.mem_union, Set.mem_ofPred_eq,
    functional_lineMap_level_iff H.leftFunctional H.left_vertex_level z positive,
    functional_lineMap_level_iff H.rightFunctional H.right_vertex_level z positive,
    functional_lineMap_le_iff H.leftFunctional H.left_vertex_level z positive,
    functional_lineMap_le_iff H.rightFunctional H.right_vertex_level z positive]

theorem local_surface_iff_carrier (z : Space)
    (near : dist z (F.toSpace Set.univ (C.vertexPoint Set.univ v)) < H.radius) :
    z ∈ F.surface ↔ z ∈ H.carrier := H.local_surface z near

end Unfoldings.SpatialFolding.VertexHinge

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem exists_tangent_range_surface_radius (v : C.Vertex Set.univ) :
    ∃ r : ℝ, 0 < r ∧ ∀ z, dist z (F.toSpace Set.univ (C.vertexPoint Set.univ v)) < r →
      (z ∈ Set.range (F.tangentToSpace Set.univ v) ↔ z ∈ F.surface) := by
  obtain ⟨N⟩ := F.exists_tangentNeighborhood Set.univ v
  obtain ⟨s, spos, star⟩ := P.exists_spatial_vertex_star_radius v
  refine ⟨min N.radius s, lt_min N.positive spos, ?_⟩
  intro z near
  constructor
  · rintro ⟨w, image⟩
    obtain ⟨⟨c, p⟩, rfl⟩ := MetricGluing.point_surjective
      (C.TangentCell Set.univ v) (C.tangentGlue Set.univ v) w
    change F.place c.val.1 p.val = z at image
    let a : C.TangentTotal Set.univ v := ⟨c, p⟩
    have radial : edist (F.toSpace Set.univ (C.vertexPoint Set.univ v)) (F.place c.val.1 p.val) =
        edist (C.tangentOrigin Set.univ v) (C.tangentPoint Set.univ v a) :=
      F.tangentToSpace_radial Set.univ v (C.tangentPoint Set.univ v a)
    have cone_near : edist (C.tangentOrigin Set.univ v) (C.tangentPoint Set.univ v a) <
        ENNReal.ofReal N.radius := by
      rw [← radial, image, edist_dist]
      apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr
      rw [dist_comm]
      exact near.trans_le (min_le_left _ _)
    exact Set.mem_iUnion.mpr ⟨c.val.1, p.val, N.inside a cone_near, image⟩
  · intro surface
    obtain ⟨c, p, hp, image⟩ := star z surface (near.trans_le (min_le_right _ _))
    let q : C.TangentCell Set.univ v c :=
      ⟨p, (C.triangle c.val.1).carrier_subset_cornerWedge c.val.2 hp⟩
    exact ⟨C.tangentFaceMap Set.univ v c q, image⟩

theorem tangent_range_eq_vertexHinge {v : C.Vertex Set.univ} (H : F.VertexHinge v) :
    Set.range (F.tangentToSpace Set.univ v) = H.carrier := by
  obtain ⟨r, positive, agrees⟩ := P.exists_tangent_range_surface_radius v
  apply eq_of_radial_local_eq (F.toSpace Set.univ (C.vertexPoint Set.univ v))
    (fun z _t ht => F.tangent_range_lineMap_iff Set.univ v z ht)
    (fun z _t ht => H.carrier_lineMap_iff z ht) (lt_min positive H.positive)
  intro z near
  exact (agrees z (near.trans_le (min_le_left _ _))).trans
    (H.local_surface_iff_carrier z (near.trans_le (min_le_right _ _)))

end Unfoldings.SpatialFolding.ConvexBoundary
