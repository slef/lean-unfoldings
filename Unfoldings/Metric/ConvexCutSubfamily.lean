module

public import Unfoldings.Metric.PolygonalBoundaryCuts

/-! Convex one-sided physical cut regions embed isometrically in the full actual cut space. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite I]
  (cells : I → Set E) (closed : ∀ i, IsClosed (cells i)) (cuts : Set E)
  (selected : I → Prop)

/-- Include the exact retained seams of a chosen cell subfamily into the full physical cut. -/
def cutSubfamilyMap :
    PolygonalCut (fun i : {i // selected i} => cells i.val) (fun i => closed i.val) cuts →
      PolygonalCut cells closed cuts :=
  lift (fun i : {i // selected i} => cells i.val)
    (cutSeams (fun i : {i // selected i} => cells i.val) (fun i => closed i.val) cuts).relation
    (fun i => of (fun i => cells i) (cutSeams cells closed cuts).relation i.val)
    (fun i => of_lipschitz _ _ i.val)
    (by
      rintro a b ⟨⟨i, j⟩, x, rfl, rfl⟩
      apply point_eq_of_glue
      exact ⟨(i.val, j.val), x, rfl, rfl⟩)

omit [NormedSpace ℝ E] in
@[simp] theorem cutSubfamilyMap_of (i : {i // selected i}) (x : cells i.val) :
    cutSubfamilyMap cells closed cuts selected
      (of (fun i : {i // selected i} => cells i.val)
        (cutSeams (fun i : {i // selected i} => cells i.val) (fun i => closed i.val) cuts).relation
        i x) = of (fun i => cells i) (cutSeams cells closed cuts).relation i.val x := rfl

omit [NormedSpace ℝ E] in
theorem cutSubfamilyMap_lipschitz : LipschitzWith 1 (cutSubfamilyMap cells closed cuts selected) :=
  lift_lipschitz _ _ _ _ _

omit [NormedSpace ℝ E] in
@[simp] theorem fold_cutSubfamilyMap
    (x : PolygonalCut (fun i : {i // selected i} => cells i.val) (fun i => closed i.val) cuts) :
    (cutSeams cells closed cuts).fold (cutSubfamilyMap cells closed cuts selected x) =
      (cutSeams (fun i : {i // selected i} => cells i.val)
        (fun i => closed i.val) cuts).fold x := by
  obtain ⟨a, rfl⟩ := point_surjective (fun i : {i // selected i} => cells i.val)
    (cutSeams (fun i : {i // selected i} => cells i.val)
      (fun i => closed i.val) cuts).relation x
  rfl

/-- The full cut metric gives the exact metric of a convex subfamily whose interior avoids cuts.
In particular, excursions through other cells cannot shorten its one-sided bank distances. -/
theorem cutSubfamilyMap_isometry {s : Set E}
    (convex : ∀ i : {i // selected i}, Convex ℝ (cells i.val))
    (full : ∀ i : {i // selected i}, (interior (cells i.val)).Nonempty)
    (cover : s = ⋃ i : {i // selected i}, cells i.val) (convex_s : Convex ℝ s)
    (cut_closed : IsClosed cuts) (outside : Disjoint (interior s) cuts) :
    Isometry (cutSubfamilyMap cells closed cuts selected) := by
  let subcells := fun i : {i // selected i} => cells i.val
  let subclosed := fun i : {i // selected i} => closed i.val
  let S := cutSeams subcells subclosed cuts
  have positions (z : PolygonalCut subcells subclosed cuts) :
      S.fold z = (cutToPolygonal subcells subclosed cuts convex cover z).val := by
    obtain ⟨a, rfl⟩ := point_surjective (fun i => subcells i) S.relation z
    rfl
  have fold_isometry : Isometry S.fold := by
    intro x y
    rw [positions x, positions y]
    have exact_distance :=
      cutToPolygonal_isometry_of_boundary_cuts subcells subclosed cuts convex full cover convex_s
        cut_closed outside x y
    rw [PolygonalPoint.edist_eq_of_segment (convex_s.segment_subset
      (cutToPolygonal subcells subclosed cuts convex cover x).property
      (cutToPolygonal subcells subclosed cuts convex cover y).property)] at exact_distance
    exact exact_distance
  intro x y
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul] using
      cutSubfamilyMap_lipschitz cells closed cuts selected x y
  · have bound := (cutSeams cells closed cuts).fold_lipschitz
      (cutSubfamilyMap cells closed cuts selected x) (cutSubfamilyMap cells closed cuts selected y)
    rw [fold_cutSubfamilyMap, fold_cutSubfamilyMap, fold_isometry.edist_eq] at bound
    simpa only [ENNReal.coe_one, one_mul] using bound

end Unfoldings.MetricGluing
