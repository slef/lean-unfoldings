module

public import Unfoldings.Topology.FirstAncestorIndex
public import Unfoldings.Geometry.OpeningCurvature
public import Unfoldings.Geometry.PolygonalRayOpening

/-! Original sources give canonical opening hinges, exact real phases and curvature budgets. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents

open PolygonalChain

variable {V : Type*} (P : AscendingParents V) {n : ℕ} (path : Fin (n + 1) → V)
  (weight : V → ℝ) (sources : List V)
  (reaches : ∀ source ∈ sources, ∃ i, P.Ancestor source (path i))

/-- Retain source order and charge each original source at its first shared path ancestor. -/
def ancestorOpenings : List (Opening n) :=
  sources.attach.map (fun source =>
    ⟨P.firstAncestorIndex path source.val (reaches source.val source.property), weight source.val⟩)

@[simp] theorem ancestorOpenings_length :
    (P.ancestorOpenings path weight sources reaches).length = sources.length := by
  simp only [ancestorOpenings, List.length_map, List.length_attach]

open Classical in
/-- The actual unreduced correction on each bank is exactly the original descendant weight. -/
theorem ancestorOpenings_heading
    (ordered : ∀ i j, i ≤ j → P.Ancestor (path i) (path j)) (i : Fin n) :
    openingHeading (P.ancestorOpenings path weight sources reaches) i =
      (sources.map (fun source =>
        if P.Ancestor source (path i.castSucc) then weight source else 0)).sum := by
  classical
  simp only [openingHeading, ancestorOpenings, List.map_map, Function.comp_def,
    P.firstAncestorIndex_le_iff path ordered]
  rw [List.attach_map_val (f := fun source : V =>
    if P.Ancestor source (path i.castSucc) then weight source else 0)]

/-- Every original source rotates the unbounded tail once. -/
theorem ancestorOpenings_tailHeading :
    openingTailHeading (P.ancestorOpenings path weight sources reaches) =
      (sources.map weight).sum := by
  simp only [openingTailHeading, ancestorOpenings, List.map_map, Function.comp_def,
    List.attach_map_val]

/-- The geometric budget is exactly the sum of the original source charges. -/
theorem ancestorOpenings_budget :
    openingBudget (P.ancestorOpenings path weight sources reaches) =
      (sources.map (fun source => |weight source|)).sum := by
  simp only [openingBudget, ancestorOpenings, List.map_map, Function.comp_def]
  rw [List.attach_map_val (f := fun source : V => |weight source|)]

/-- Distinct original sources give the total-weight bound without a charge assignment input. -/
theorem ancestorOpenings_budget_le_total [Fintype V] (nonnegative : ∀ v, 0 ≤ weight v)
    (distinct : sources.Nodup) :
    openingBudget (P.ancestorOpenings path weight sources reaches) ≤ ∑ v, weight v := by
  classical
  calc
    _ = (sources.map weight).sum := by
      rw [P.ancestorOpenings_budget]
      simp only [abs_of_nonneg (nonnegative _)]
    _ = ∑ v ∈ sources.toFinset, weight v := (List.sum_toFinset weight distinct).symm
    _ ≤ ∑ v, weight v := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun v _ _ => nonnegative v)

/-- Every geometric event carries the weight of its actual named original source. -/
theorem ancestorOpenings_angles_nonnegative (nonnegative : ∀ v, 0 ≤ weight v)
    (event : Opening n) (member : event ∈ P.ancestorOpenings path weight sources reaches) :
    0 ≤ event.angle := by
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp member
  exact nonnegative source.val

end Unfoldings.AscendingParents
