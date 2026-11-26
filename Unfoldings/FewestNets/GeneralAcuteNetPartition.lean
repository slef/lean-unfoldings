module

public import Unfoldings.FewestNets.LatitudeIntervalCertificate
public import Unfoldings.FewestNets.TightLatitudeNetPartition

/-! The general acute-angle theorem of Fewest Nets. -/

@[expose] public section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets RevisedLatitudeGrid Real

universe u v

/-- A convex polyhedron with a conforming triangular boundary mesh whose
corner angles are at most `π / 2 - a` partitions into fewer than `246.3 / a^4`
nonoverlapping nets along the original triangle edges. -/
theorem exists_acute_netPartition_lt_246_3 {Face : Type u} [Fintype Face]
    {C : TriangleComplex.{u, v} Face} {F : SpatialFolding C} (P : F.ConvexBoundary)
    {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ π / 2 - a) :
    ∃ n : ℕ, (n : ℝ) < 246.3 / a ^ 4 ∧ C.HasNetPartition n :=
  P.exists_acute_netPartition_lt_246_3_of_count positive small angles
    (fun h => normalizedGridCoefficient_lt (by linarith only [h]) small)

end Unfoldings.SpatialFolding.ConvexBoundary
