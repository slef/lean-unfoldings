module

public import Unfoldings.Polyhedron.Chords
public import Unfoldings.Complex.Regular
public import Unfoldings.Metric.BallParametrization

/-!
# Constructed intrinsic charts from whole planar spatial patches

The embedded inverse is isometric on the convex planar patch. Ambient
nonexpansion and local plane coverage make its image the whole intrinsic
ball, so this constructs a metric chart rather than just a surface picture.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem isRegularPoint_of_planar_patch (place : Plane →ᵃⁱ[ℝ] Space) (p : Plane)
    (x : C.Realization Set.univ) (center : place p = F.toSpace Set.univ x)
    {r : ℝ} (positive : 0 < r) (included : place '' Metric.ball p r ⊆ F.surface)
    (near_plane : ∀ z ∈ F.surface, dist z (place p) < r → z ∈ Set.range place) :
    C.IsRegularPoint Set.univ x := by
  let s := place '' Metric.ball p r
  have convex : Convex ℝ s := (convex_ball p r).affine_image place.toAffineMap
  let toSlice (q : Metric.ball p r) : s := ⟨place q.val, q.val, q.property, rfl⟩
  have slice_isometry : Isometry toSlice := fun q w => place.isometry q.val w.val
  let param : Metric.ball p r → C.Realization Set.univ := P.liftSpatial s included ∘ toSlice
  have isometry : Isometry param := (P.liftSpatial_isometry s convex included).comp slice_isometry
  have at_center : param ⟨p, Metric.mem_ball_self positive⟩ = x := by
    apply P.embedded
    change F.toSpace Set.univ (P.liftSpatial s included (toSlice _)) = _
    rw [P.toSpace_liftSpatial]
    exact center
  apply HasMetricBallChart.of_isometric_ball positive param isometry at_center
  intro y near
  have nonexpanding := (F.toSpace_lipschitz Set.univ).edist_le_mul y x
  have spatial_near : edist (F.toSpace Set.univ y) (place p) < ENNReal.ofReal r := by
    rw [center]
    have bound : edist (F.toSpace Set.univ y) (F.toSpace Set.univ x) ≤ edist y x := by
      simpa only [ENNReal.coe_one, one_mul] using nonexpanding
    exact bound.trans_lt near
  have distance_near : dist (F.toSpace Set.univ y) (place p) < r := by
    rw [edist_dist] at spatial_near
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp spatial_near
  obtain ⟨q, coordinates⟩ := near_plane (F.toSpace Set.univ y)
    ((F.range_toSpace Set.univ).le ⟨y, rfl⟩) distance_near
  have q_near : dist q p < r := by
    rw [← coordinates, place.isometry.dist_eq] at distance_near
    exact distance_near
  refine ⟨⟨q, Metric.mem_ball.mpr q_near⟩, ?_⟩
  apply P.embedded
  change F.toSpace Set.univ (P.liftSpatial s included (toSlice _)) = _
  rw [P.toSpace_liftSpatial]
  exact coordinates

end Unfoldings.SpatialFolding.ConvexBoundary
