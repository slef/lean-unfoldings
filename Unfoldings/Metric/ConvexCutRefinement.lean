module

public import Unfoldings.Metric.PhysicalCutRefinementEquiv
public import Unfoldings.Metric.CutIsometricCoverMap

/-! Convex geometric subdivisions supply physical cut refinement without metric certificates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {E I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite I] [Finite J]
  (coarse : I → Set E) (fine : J → Set E) (closed : ∀ j, IsClosed (fine j)) (cuts : Set E)

/-- Full convex fine cells covering each convex original cell preserve its cut metric
when the original cell interior avoids cuts. All local metric data are derived. -/
def convexBoundaryCutRefinement (parent : J → I)
    (included : ∀ j, fine j ⊆ coarse (parent j))
    (cover : ∀ i, coarse i = ⋃ j : {j // parent j = i}, fine j.val)
    (convex_fine : ∀ j, Convex ℝ (fine j))
    (full : ∀ j, (interior (fine j)).Nonempty)
    (convex_coarse : ∀ i, Convex ℝ (coarse i)) (cut_closed : IsClosed cuts)
    (outside : ∀ i, Disjoint (interior (coarse i)) cuts) :
    PhysicalCutRefinement coarse fine closed cuts where
  parent := parent
  included := included
  cover := cover
  fold_isometry i := cut_fold_isometry_of_boundary_cuts
    (fun j : {j // parent j = i} => fine j.val) (fun j => closed j.val) (fun x : E => x) cuts
    (fun j => convex_fine j.val) (fun j => full j.val) (cover i) (convex_coarse i)
    cut_closed (outside i)

end Unfoldings.MetricGluing
