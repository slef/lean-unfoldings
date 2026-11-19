module

public import Unfoldings.Metric.PhysicalSeamsDiagonal
public import Unfoldings.Metric.PolygonalBoundaryCover

/-! Coinciding closed cells have literal closed isometric seam domains. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {I E : Type*} [Finite I] [NormedAddCommGroup E] [NormedSpace ℝ E]
  (cells : I → Set E) (closed : ∀ i, IsClosed (cells i))

/-- Retain each physical intersection as its actual seam domain. -/
def coincidentPhysicalSeams : PhysicalSeams cells where
  carrier i j := cells i ∩ cells j
  closed i j := (closed i).inter (closed j)
  subset_left _ _ := Set.inter_subset_left
  subset_right _ _ := Set.inter_subset_right

omit [NormedSpace ℝ E] in
/-- Intersection domains declare precisely the original physical coincidences. -/
theorem coincidentPhysicalSeams_relation (x y : Total (fun i => cells i)) :
    (coincidentPhysicalSeams cells closed).relation x y ↔ coincident cells x y := by
  constructor
  · intro joined
    exact (coincidentPhysicalSeams cells closed).physical_eq_of_eqvGen
      (Relation.EqvGen.rel _ _ joined)
  · intro same
    refine ⟨(x.1, y.1), ⟨x.2.val, x.2.property, same ▸ y.2.property⟩, rfl, ?_⟩
    exact congrArg (Sigma.mk y.1) (Subtype.ext same.symm)

/-- Omit identity seams while preserving literal closed domains on distinct cells. -/
def distinctCoincidentClosedSeams : ClosedSeams (fun i => cells i) :=
  (coincidentPhysicalSeams cells closed).offDiagonal.closedSeams

omit [NormedSpace ℝ E] in
/-- The closed-domain construction retains the exact boundary-only coincidence relation. -/
theorem distinctCoincidentClosedSeams_relation (x y : Total (fun i => cells i)) :
    (distinctCoincidentClosedSeams cells closed).relation x y ↔
      distinctCoincident cells x y := by
  exact ((coincidentPhysicalSeams cells closed).offDiagonal_relation_iff x y).trans
    (and_congr_right (fun _ => coincidentPhysicalSeams_relation cells closed x y))

end Unfoldings.MetricGluing
