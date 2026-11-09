module

public import Unfoldings.Cone.SmallDilation
public import Unfoldings.Cone.Neighborhood
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Spatial embeddings of actual uncut tangent fans

Spatial folding preserves every apex distance. If the original uncut
surface is embedded, its full tangent fan is embedded as well: shrink two
hypothetically coincident spatial points into the constructed exact tangent
neighborhood, use the original embedding there, then undo the dilation.
-/

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

theorem tangentToSpace_radial (retain : Set C.Seam) (v : C.Vertex retain)
    (z : C.TangentFan retain v) :
    edist (F.toSpace retain (C.vertexPoint retain v)) (F.tangentToSpace retain v z) =
      edist (C.tangentOrigin retain v) z := by
  obtain ⟨⟨c, x⟩, rfl⟩ := MetricGluing.point_surjective
    (C.TangentCell retain v) (C.tangentGlue retain v) z
  change edist (F.toSpace retain (C.vertexPoint retain v)) (F.place c.val.1 x.val) =
    edist (C.tangentOrigin retain v) (C.tangentFaceMap retain v c x)
  rw [C.tangent_edist_origin_faceMap, ← F.tangentApex_spatial_eq retain v c]
  exact (F.place c.val.1).isometry.edist_eq _ _

theorem tangentToSpace_injective (embedded : F.IsEmbedded) (v : C.Vertex Set.univ) :
    Function.Injective (F.tangentToSpace Set.univ v) := by
  intro z w image
  obtain ⟨⟨c, x⟩, rfl⟩ := MetricGluing.point_surjective
    (C.TangentCell Set.univ v) (C.tangentGlue Set.univ v) z
  obtain ⟨⟨d, y⟩, rfl⟩ := MetricGluing.point_surjective
    (C.TangentCell Set.univ v) (C.tangentGlue Set.univ v) w
  change F.place c.val.1 x.val = F.place d.val.1 y.val at image
  obtain ⟨N⟩ := F.exists_tangentNeighborhood Set.univ v
  obtain ⟨t, nonzero, near_x, near_y⟩ :=
    C.exists_tangentDilate_near_pair Set.univ v N.radius N.positive
      (C.tangentFaceMap Set.univ v c x) (C.tangentFaceMap Set.univ v d y)
  let a : C.TangentTotal Set.univ v := ⟨c, C.tangentCellDilate Set.univ v c t x⟩
  let b : C.TangentTotal Set.univ v := ⟨d, C.tangentCellDilate Set.univ v d t y⟩
  change edist (C.tangentOrigin Set.univ v) (C.tangentPoint Set.univ v a) <
    ENNReal.ofReal N.radius at near_x
  change edist (C.tangentOrigin Set.univ v) (C.tangentPoint Set.univ v b) <
    ENNReal.ofReal N.radius at near_y
  have original : C.tangentSurfaceTag Set.univ v a = C.tangentSurfaceTag Set.univ v b := by
    apply embedded
    rw [C.tangentSurfaceTag_of_mem Set.univ v a (N.inside a near_x),
      C.tangentSurfaceTag_of_mem Set.univ v b (N.inside b near_y),
      F.toSpace_faceMap, F.toSpace_faceMap]
    change F.place c.val.1 (AffineMap.lineMap (C.tangentApex Set.univ v c).val x.val (t : ℝ)) =
      F.place d.val.1 (AffineMap.lineMap (C.tangentApex Set.univ v d).val y.val (t : ℝ))
    rw [F.place_lineMap, F.place_lineMap, F.tangentApex_spatial_eq,
      F.tangentApex_spatial_eq, image]
  apply (C.tangentDilateHomeomorph Set.univ v t nonzero).injective
  change C.tangentPoint Set.univ v a = C.tangentPoint Set.univ v b
  apply edist_eq_zero.mp
  have exact_distance := N.exact_distance a b near_x near_y
  rw [original, edist_self] at exact_distance
  exact exact_distance.symm

/-- Spatial tangent folding is proper even when cuts make it noninjective. -/
theorem tangentToSpace_isProperMap (retain : Set C.Seam) (v : C.Vertex retain) :
    IsProperMap (F.tangentToSpace retain v) := by
  have radial : (dist (F.toSpace retain (C.vertexPoint retain v))) ∘
      F.tangentToSpace retain v = dist (C.tangentOrigin retain v) := by
    funext z
    change dist (F.toSpace retain (C.vertexPoint retain v)) (F.tangentToSpace retain v z) =
      dist (C.tangentOrigin retain v) z
    have equal := congrArg ENNReal.toReal (F.tangentToSpace_radial retain v z)
    simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using equal
  apply isProperMap_of_comp_of_t2 (g := dist (F.toSpace retain (C.vertexPoint retain v)))
    (F.tangentToSpace_lipschitz retain v).continuous (continuous_const.dist continuous_id)
  rw [radial]
  exact isProperMap_dist _

theorem tangentToSpace_isClosedEmbedding (embedded : F.IsEmbedded) (v : C.Vertex Set.univ) :
    Topology.IsClosedEmbedding (F.tangentToSpace Set.univ v) :=
  .of_continuous_injective_isClosedMap (F.tangentToSpace_lipschitz Set.univ v).continuous
    (F.tangentToSpace_injective embedded v) (F.tangentToSpace_isProperMap Set.univ v).isClosedMap

end Unfoldings.SpatialFolding
