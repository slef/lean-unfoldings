module

public import Unfoldings.Cone.LinkComparison
public import Unfoldings.Cone.AngularHeadingShortcut

/-!
# Angular shortcuts in actual tangent fans

The angular-to-tangent comparison is nonexpanding and preserves every radial
distance. Strict angular chord shortcuts therefore remain strict in the
actual route metric, independently of any spatial folding.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

theorem angularToTangent_dist_origin {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (z : (C.linkAngularFan retain v chain).Surface) :
    dist (C.tangentOrigin retain v) (C.angularToTangent retain v chain z) =
      dist (C.linkAngularFan retain v chain).origin z := by
  have equal := congrArg ENNReal.toReal (C.angularToTangent_radial retain v chain z)
  simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using equal

/-- A pointed heading interval inside an ordered fan supplies an actual
strict tangent-metric shortcut. No inverse comparison or folding is assumed. -/
theorem tangent_dist_lt_via_origin_of_headingSector {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n)
    (full_bound : (C.linkAngularFan retain v chain).totalAngle < 2 * Real.pi)
    (a b : ℝ) (positive : 0 < b - a) (small : b - a < Real.pi)
    (first : 0 ≤ a) (last : b ≤ (C.linkAngularFan retain v chain).totalAngle)
    {x y : (C.linkAngularFan retain v chain).Surface}
    (left : (C.linkAngularFan retain v chain).develop x ∈ headingSector a b)
    (right : (C.linkAngularFan retain v chain).develop y ∈ headingSector a b)
    (left_nonzero : x ≠ (C.linkAngularFan retain v chain).origin)
    (right_nonzero : y ≠ (C.linkAngularFan retain v chain).origin) :
    dist (C.angularToTangent retain v chain x) (C.angularToTangent retain v chain y) <
      dist (C.angularToTangent retain v chain x) (C.tangentOrigin retain v) +
        dist (C.tangentOrigin retain v) (C.angularToTangent retain v chain y) := by
  have strict := (C.linkAngularFan retain v chain).dist_lt_via_origin_of_mem_headingSector
    full_bound a b positive small first last left right left_nonzero right_nonzero
  have bound := (C.angularToTangent_lipschitz retain v chain).dist_le_mul x y
  simp only [NNReal.coe_one, one_mul] at bound
  apply bound.trans_lt
  rw [dist_comm (C.angularToTangent retain v chain x) (C.tangentOrigin retain v),
    C.angularToTangent_dist_origin, C.angularToTangent_dist_origin]
  simpa only [dist_comm] using strict

end Unfoldings.TriangleComplex
