module

public import Unfoldings.Metric.PhysicalCutRefinementSeams

/-! Actual per-cell subdivisions preserve the complete physical cut metric and its copies. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing.PhysicalCutRefinement

variable {E I J : Type*} [NormedAddCommGroup E] [Finite I] [Finite J]
  {coarse : I → Set E} {fine : J → Set E} {closed : ∀ j, IsClosed (fine j)} {cuts : Set E}
  (R : PhysicalCutRefinement coarse fine closed cuts) (coarse_closed : ∀ i, IsClosed (coarse i))

/-- The canonical physical map sends each fine cut copy to its original parent copy. -/
def coarsen : PolygonalCut fine closed cuts → PolygonalCut coarse coarse_closed cuts :=
  cutCoverMap fine closed coarse coarse_closed R.parent R.included cuts

/-- Reconstruct the whole original cut from its actual fine physical cells. -/
def refine : PolygonalCut coarse coarse_closed cuts → PolygonalCut fine closed cuts :=
  lift (fun i => coarse i) (cutSeams coarse coarse_closed cuts).relation R.refinedCellMap
    R.refinedCellMap_lipschitz (R.refinedCellMap_compatible coarse_closed)

theorem refine_lipschitz : LipschitzWith 1 (R.refine coarse_closed) := lift_lipschitz _ _ _ _ _

theorem coarsen_lipschitz : LipschitzWith 1 (R.coarsen coarse_closed) :=
  cutCoverMap_lipschitz fine closed coarse coarse_closed R.parent R.included cuts

theorem refine_coarsen (x : PolygonalCut fine closed cuts) :
    R.refine coarse_closed (R.coarsen coarse_closed x) = x := by
  obtain ⟨⟨j, p⟩, rfl⟩ := point_surjective (fun j => fine j) (cutSeams fine closed cuts).relation x
  exact R.refinedCellMap_of j p

theorem coarsen_surjective : Function.Surjective (R.coarsen coarse_closed) := by
  intro x
  obtain ⟨⟨i, p⟩, rfl⟩ := point_surjective (fun i => coarse i)
    (cutSeams coarse coarse_closed cuts).relation x
  have covered : p.val ∈ ⋃ j : {j // R.parent j = i}, fine j.val :=
    Eq.mp (congrArg (fun s : Set E => p.val ∈ s) (R.cover i)) p.property
  obtain ⟨⟨j, parent⟩, member⟩ := Set.mem_iUnion.mp covered
  refine ⟨of (fun j => fine j) (cutSeams fine closed cuts).relation j ⟨p.val, member⟩, ?_⟩
  change point (fun i => coarse i) (cutSeams coarse coarse_closed cuts).relation
    ⟨R.parent j, ⟨p.val, R.included j member⟩⟩ =
      point (fun i => coarse i) (cutSeams coarse coarse_closed cuts).relation ⟨i, p⟩
  apply congrArg (point (fun i => coarse i) (cutSeams coarse coarse_closed cuts).relation)
  cases parent
  rfl

theorem coarsen_refine (x : PolygonalCut coarse coarse_closed cuts) :
    R.coarsen coarse_closed (R.refine coarse_closed x) = x := by
  obtain ⟨y, rfl⟩ := R.coarsen_surjective coarse_closed x
  exact congrArg (R.coarsen coarse_closed) (R.refine_coarsen coarse_closed y)

/-- Subdividing actual physical cut cells preserves the entire cut metric.
Compatibility on old closed seams is derived, and all original cut-bank copies survive. -/
def isometryEquiv : PolygonalCut fine closed cuts ≃ᵢ PolygonalCut coarse coarse_closed cuts where
  toFun := R.coarsen coarse_closed
  invFun := R.refine coarse_closed
  left_inv := R.refine_coarsen coarse_closed
  right_inv := R.coarsen_refine coarse_closed
  isometry_toFun := by
    intro x y
    apply le_antisymm
    · exact (R.coarsen_lipschitz coarse_closed x y).trans_eq (one_mul _)
    · have bound := R.refine_lipschitz coarse_closed
        (R.coarsen coarse_closed x) (R.coarsen coarse_closed y)
      have equal : edist x y = edist
          (R.refine coarse_closed (R.coarsen coarse_closed x))
          (R.refine coarse_closed (R.coarsen coarse_closed y)) :=
        congrArg₂ edist (R.refine_coarsen coarse_closed x).symm
          (R.refine_coarsen coarse_closed y).symm
      exact equal.trans_le (bound.trans_eq (one_mul _))

/-- The isometry retains each specified original parent-cell copy. -/
@[simp] theorem isometryEquiv_of (j : J) (p : fine j) :
    R.isometryEquiv coarse_closed (of (fun j => fine j) (cutSeams fine closed cuts).relation j p) =
      of (fun i => coarse i) (cutSeams coarse coarse_closed cuts).relation (R.parent j)
        ⟨p.val, R.included j p.property⟩ := rfl

theorem fold_isometryEquiv (x : PolygonalCut fine closed cuts) :
    (cutSeams coarse coarse_closed cuts).fold (R.isometryEquiv coarse_closed x) =
      (cutSeams fine closed cuts).fold x :=
  fold_cutCoverMap fine closed coarse coarse_closed R.parent R.included cuts x

end Unfoldings.MetricGluing.PhysicalCutRefinement
