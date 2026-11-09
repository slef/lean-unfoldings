module

public import Unfoldings.Cone.CyclicIsometry
public import Unfoldings.Cone.Charts
public import Unfoldings.Metric.BallIsometry

/-!
# Constructed Euclidean charts at actual flat vertices

A cyclic vertex with genuine total angle two pi has a tangent fan isometric
to the Euclidean plane. For a spatially folded triangle complex, the proved
whole-ball tangent comparison transfers that isometry to the original
intrinsic surface, retaining agreement with every incident face coordinate.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

structure FlatVertexChart where
  radius : ℝ
  positive : 0 < radius
  frame : C.TangentFan retain v ≃ᵢ Plane
  frame_origin : frame (C.tangentOrigin retain v) = 0
  chart : Metric.eball (0 : Plane) (ENNReal.ofReal radius) ≃ᵢ
    Metric.eball (C.vertexPoint retain v) (ENNReal.ofReal radius)
  agrees : ∀ (a : C.TangentTotal retain v)
    (near : edist (C.tangentPoint retain v a) (C.tangentOrigin retain v) <
      ENNReal.ofReal radius),
    (chart ⟨frame (C.tangentPoint retain v a), by
      change edist (frame (C.tangentPoint retain v a)) (0 : Plane) < ENNReal.ofReal radius
      rw [← frame_origin, frame.isometry.edist_eq]
      exact near⟩).val = C.tangentSurfaceTag retain v a

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (retain : Set C.Seam) (v : C.Vertex retain)

include F

theorem exists_flatVertexChart (interior : ¬ C.IsBoundaryVertex retain v)
    (flat : C.totalAngle retain v = 2 * Real.pi) : Nonempty (C.FlatVertexChart retain v) := by
  obtain ⟨N⟩ := F.exists_tangentChart retain v
  obtain ⟨e, origin⟩ := C.exists_flatFanIsometry_origin retain v interior flat
  let frame : C.TangentFan retain v ≃ᵢ Plane :=
    e.trans Complex.orthonormalBasisOneI.repr.toIsometryEquiv
  have center : frame (C.tangentOrigin retain v) = 0 := by
    change Complex.orthonormalBasisOneI.repr (e (C.tangentOrigin retain v)) = 0
    rw [origin, map_zero]
  let balls := basedEBallIsometry frame (C.tangentOrigin retain v) 0 center
    (ENNReal.ofReal N.radius)
  refine ⟨⟨N.radius, N.positive, frame, center, balls.symm.trans N.chart, ?_⟩⟩
  intro a near
  have plane_near : edist (frame (C.tangentPoint retain v a)) (0 : Plane) <
      ENNReal.ofReal N.radius := by
    rw [← center, frame.isometry.edist_eq]
    exact near
  let y : Metric.eball (0 : Plane) (ENNReal.ofReal N.radius) :=
    ⟨frame (C.tangentPoint retain v a), plane_near⟩
  have back : balls.symm y = ⟨C.tangentPoint retain v a, near⟩ := by
    apply Subtype.ext
    exact frame.symm_apply_apply (C.tangentPoint retain v a)
  change (N.chart (balls.symm y)).val = C.tangentSurfaceTag retain v a
  rw [back]
  exact N.agrees a near

/-- Choose a flat chart after proving its existence from the actual surface metric. -/
def flatVertexChart (interior : ¬ C.IsBoundaryVertex retain v)
    (flat : C.totalAngle retain v = 2 * Real.pi) : C.FlatVertexChart retain v :=
  Classical.choice (F.exists_flatVertexChart retain v interior flat)

end Unfoldings.SpatialFolding
