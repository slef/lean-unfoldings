module

public import Unfoldings.Geometry.FrontierOpeningHistory
public import Unfoldings.Geometry.OpeningFilterZero
public import Unfoldings.Topology.ParentHistorySources

/-! Canonical nonzero bank openings from the actual first-contact source history. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents

open PolygonalChain

variable {V : Type*} [Fintype V] (P : AscendingParents V) (seeds : List V)
  (root : {v // v ∈ P.roots}) {n : ℕ} (path : Fin (n + 1) → V)
  (last : path (Fin.last n) = root.val) (weight : V → ℝ)

/-- Original first-contact order, first shared-ancestor hinges, and no artificial flat openings. -/
def historyOpenings : List (Opening n) :=
  withoutZeroOpenings (P.ancestorOpenings path weight (P.historySources seeds root)
    (fun source member => ⟨Fin.last n,
      last.symm ▸ P.historySources_ancestor seeds root source member⟩))

open Classical in
/-- Canonical real phases are actual processed descendant weights; source coverage is derived. -/
theorem historyOpenings_heading
    (ordered : ∀ i j, i ≤ j → P.Ancestor (path i) (path j)) (i : Fin n) :
    openingHeading (P.historyOpenings seeds root path last weight) i =
      ((P.initialFrontier).run seeds).processedDescendantWeight weight (path i.castSucc) := by
  unfold historyOpenings
  rw [withoutZeroOpenings_heading]
  apply ParentFrontier.ancestorOpenings_heading_eq_processedWeight
    ((P.initialFrontier).run seeds) path weight (P.historySources seeds root) _ ordered
    (P.historySources_nodup seeds root) _ i
  intro source
  simpa only [last] using P.mem_historySources seeds root source

/-- Curvature is spent once over the original history, independently of repeated input seeds. -/
theorem historyOpenings_budget_le_total (nonnegative : ∀ v, 0 ≤ weight v) :
    openingBudget (P.historyOpenings seeds root path last weight) ≤ ∑ v, weight v := by
  unfold historyOpenings
  rw [withoutZeroOpenings_budget]
  exact P.ancestorOpenings_budget_le_total path weight (P.historySources seeds root) _
    nonnegative (P.historySources_nodup seeds root)

/-- All remaining events are genuinely positive whenever original weights are nonnegative. -/
theorem historyOpenings_positive (nonnegative : ∀ v, 0 ≤ weight v)
    (event : Opening n) (member : event ∈ P.historyOpenings seeds root path last weight) :
    0 < event.angle :=
  withoutZeroOpenings_positive _ (P.ancestorOpenings_angles_nonnegative path weight
    (P.historySources seeds root) _ nonnegative) event member

end Unfoldings.AscendingParents
