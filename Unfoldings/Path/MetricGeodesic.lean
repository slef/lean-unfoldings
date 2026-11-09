module

public import Unfoldings.Path.ConvexChart

/-! Real distance formulas for constant-speed metric geodesics. -/

@[expose] public section

open scoped ENNReal

namespace Path

variable {X : Type*} [MetricSpace X] {a b : X} {p : Path a b}

theorem IsGeodesic.dist_eq (geodesic : p.IsGeodesic) (s t : unitInterval) :
    dist (p s) (p t) = dist a b * dist s t := by
  have equal := congrArg ENNReal.toReal (geodesic s t)
  simpa only [edist_dist, ENNReal.toReal_mul, ENNReal.toReal_ofReal dist_nonneg] using equal

theorem IsGeodesic.dist_source (geodesic : p.IsGeodesic) (t : unitInterval) :
    dist a (p t) = dist a b * (t : ℝ) := by
  have equal := geodesic.dist_eq 0 t
  simpa only [Path.source, Subtype.dist_eq, Real.dist_eq, Set.Icc.coe_zero,
    zero_sub, abs_neg, abs_of_nonneg t.property.1] using equal

theorem IsGeodesic.dist_target (geodesic : p.IsGeodesic) (t : unitInterval) :
    dist (p t) b = dist a b * (1 - (t : ℝ)) := by
  have equal := geodesic.dist_eq t 1
  simpa only [Path.target, Subtype.dist_eq, Real.dist_eq, Set.Icc.coe_one,
    abs_of_nonpos (sub_nonpos.mpr t.property.2), neg_sub] using equal

end Path
