module

public import Unfoldings.Metric.PhysicalCutRefinement

/-! Original separately closed cut seams survive reconstruction from actual fine cells. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing.PhysicalCutRefinement

variable {E I J : Type*} [NormedAddCommGroup E] [Finite I] [Finite J]
  {coarse : I → Set E} {fine : J → Set E} {closed : ∀ j, IsClosed (fine j)} {cuts : Set E}
  (R : PhysicalCutRefinement coarse fine closed cuts) (coarse_closed : ∀ i, IsClosed (coarse i))

omit [Finite I] in
/-- Agreement off the actual cut extends to each separately closed original seam. -/
theorem refinedCellMap_eq_on_carrier (i j : I) (z : E)
    (member : z ∈ (cutSeams coarse coarse_closed cuts).carrier i j) :
    R.refinedCellMap i ⟨z, (cutSeams coarse coarse_closed cuts).subset_left i j member⟩ =
      R.refinedCellMap j ⟨z, (cutSeams coarse coarse_closed cuts).subset_right i j member⟩ := by
  let U := coarse i ∩ coarse j
  let left (p : U) := R.refinedCellMap i ⟨p.val, p.property.1⟩
  let right (p : U) := R.refinedCellMap j ⟨p.val, p.property.2⟩
  have left_bound : LipschitzWith 1 left := fun p q => R.refinedCellMap_lipschitz i _ _
  have right_bound : LipschitzWith 1 right := fun p q => R.refinedCellMap_lipschitz j _ _
  let uncut : Set U := {p | p.val ∉ cuts}
  have same : Set.EqOn left right uncut := by
    intro p outside
    apply cut_eq_of_fold_eq_outside fine closed cuts
    · exact (R.fold_refinedCellMap i ⟨p.val, p.property.1⟩).trans
        (R.fold_refinedCellMap j ⟨p.val, p.property.2⟩).symm
    · exact fun member => outside (Eq.mp (congrArg (fun z : E => z ∈ cuts)
        (R.fold_refinedCellMap i ⟨p.val, p.property.1⟩)) member)
  let point : U := ⟨z, (cutSeams coarse coarse_closed cuts).subset_left i j member,
    (cutSeams coarse coarse_closed cuts).subset_right i j member⟩
  have image : Subtype.val '' uncut = (coarse i ∩ coarse j) \ cuts := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.property, hq⟩
    · intro hp
      exact ⟨⟨p, hp.1⟩, hp.2, rfl⟩
  have near : point ∈ closure uncut := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    change z ∈ closure (Subtype.val '' uncut)
    rw [image]
    exact member
  exact same.closure left_bound.continuous right_bound.continuous near

/-- The original actual seam relation needs no compatibility certificate from the subdivision. -/
theorem refinedCellMap_compatible (a b : Total (fun i => coarse i))
    (joined : (cutSeams coarse coarse_closed cuts).relation a b) :
    R.refinedCellMap a.1 a.2 = R.refinedCellMap b.1 b.2 := by
  obtain ⟨⟨i, j⟩, x, rfl, rfl⟩ := joined
  exact R.refinedCellMap_eq_on_carrier coarse_closed i j x.val x.property

end Unfoldings.MetricGluing.PhysicalCutRefinement
