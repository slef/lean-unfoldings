module

public import Unfoldings.Cone.Radial
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Properness and completeness of tangent fans

Exact radial distance identifies each closed ball about the origin with the
finite union of the corresponding compact wedge balls. Arbitrary closed balls
are closed subsets of larger origin balls.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

instance (c : C.CornerAt retain v) : ProperSpace (C.TangentCell retain v c) :=
  ProperSpace.of_isClosed ((C.triangle c.val.1).isClosed_cornerWedge c.val.2)

theorem tangent_dist_origin_faceMap (c : C.CornerAt retain v) (x : C.TangentCell retain v c) :
    dist (C.tangentOrigin retain v) (C.tangentFaceMap retain v c x) =
      dist (C.tangentApex retain v c) x := by
  have equal := C.tangent_edist_origin_faceMap retain v c x
  rw [edist_dist, edist_dist] at equal
  have real_equal := congrArg ENNReal.toReal equal
  simpa only [ENNReal.toReal_ofReal dist_nonneg] using real_equal

theorem tangentRadius_eq_dist_origin (x : C.TangentFan retain v) :
    C.tangentRadius retain v x = dist (C.tangentOrigin retain v) x := by
  obtain ⟨⟨c, x⟩, rfl⟩ := MetricGluing.point_surjective (C.TangentCell retain v)
    (C.tangentGlue retain v) x
  change C.tangentRadius retain v (C.tangentFaceMap retain v c x) =
    dist (C.tangentOrigin retain v) (C.tangentFaceMap retain v c x)
  rw [C.tangentRadius_faceMap, C.tangent_dist_origin_faceMap]
  exact dist_comm _ _

theorem tangentFaceMap_preimage_ball (c : C.CornerAt retain v) (r : ℝ) :
    C.tangentFaceMap retain v c ⁻¹' Metric.ball (C.tangentOrigin retain v) r =
      Metric.ball (C.tangentApex retain v c) r := by
  ext x
  change dist (C.tangentFaceMap retain v c x) (C.tangentOrigin retain v) < r ↔
    dist x (C.tangentApex retain v c) < r
  rw [dist_comm (C.tangentFaceMap retain v c x), C.tangent_dist_origin_faceMap, dist_comm]

/-- Every closed origin ball is precisely the union of the original closed wedge balls. -/
theorem tangent_closedBall_origin_eq (r : ℝ) :
    Metric.closedBall (C.tangentOrigin retain v) r =
      ⋃ c, C.tangentFaceMap retain v c '' Metric.closedBall (C.tangentApex retain v c) r := by
  ext x
  constructor
  · intro inside
    obtain ⟨⟨c, y⟩, rfl⟩ := MetricGluing.point_surjective (C.TangentCell retain v)
      (C.tangentGlue retain v) x
    change dist (C.tangentFaceMap retain v c y) (C.tangentOrigin retain v) ≤ r at inside
    rw [dist_comm (C.tangentFaceMap retain v c y),
      C.tangent_dist_origin_faceMap, dist_comm] at inside
    exact Set.mem_iUnion.mpr ⟨c, y, inside, rfl⟩
  · intro inside
    obtain ⟨c, y, hy, rfl⟩ := Set.mem_iUnion.mp inside
    change dist (C.tangentFaceMap retain v c y) (C.tangentOrigin retain v) ≤ r
    rw [dist_comm (C.tangentFaceMap retain v c y), C.tangent_dist_origin_faceMap, dist_comm]
    exact hy

theorem compact_tangent_closedBall_origin (r : ℝ) :
    IsCompact (Metric.closedBall (C.tangentOrigin retain v) r) := by
  rw [C.tangent_closedBall_origin_eq]
  exact isCompact_iUnion fun c => (isCompact_closedBall (C.tangentApex retain v c) r).image
    (C.tangentFaceMap_lipschitz retain v c).continuous

/-- The constructed tangent metric is proper; completeness follows from Mathlib. -/
instance : ProperSpace (C.TangentFan retain v) where
  isCompact_closedBall x r :=
    (C.compact_tangent_closedBall_origin retain v
      (r + dist x (C.tangentOrigin retain v))).of_isClosed_subset Metric.isClosed_closedBall
        (Metric.closedBall_subset_closedBall' le_rfl)

theorem completeSpace_tangentFan : CompleteSpace (C.TangentFan retain v) := inferInstance

end Unfoldings.TriangleComplex
