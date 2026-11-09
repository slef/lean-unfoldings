module

public import Unfoldings.Metric.Polygonal
public import Unfoldings.Path.Distance
public import Unfoldings.Path.Segment
public import Unfoldings.Path.Restriction

/-!
# Continuous paths realize the polygonal metric

Every allowed step has an actual straight geodesic. Concatenating them shows
that route distance agrees with the infimum of continuous-path lengths.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.PolygonalPoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : Set E} {x y : PolygonalPoint s}

def segmentPath (inside : segment ℝ x.val y.val ⊆ s) : Path x y where
  toFun t := ⟨Path.segment x.val y.val t,
    inside (lineMap_mem_segment ℝ x.val y.val t.property)⟩
  continuous_toFun :=
    (includeConvex_isometry (segment ℝ x.val y.val) (convex_segment _ _) inside).continuous.comp
      ((Path.segment x.val y.val).continuous.subtype_mk
        (fun t => lineMap_mem_segment ℝ x.val y.val t.property))
  source' := PolygonalPoint.ext (Path.segment x.val y.val).source
  target' := PolygonalPoint.ext (Path.segment x.val y.val).target

theorem segmentPath_isGeodesic (inside : segment ℝ x.val y.val ⊆ s) :
    (segmentPath inside).IsGeodesic := by
  let q := (Path.segment x.val y.val).codRestrict (segment ℝ x.val y.val)
    (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
    (fun t => lineMap_mem_segment ℝ x.val y.val t.property)
  let f := includeConvex (segment ℝ x.val y.val) inside
  have isometry : Isometry f := includeConvex_isometry _ (convex_segment _ _) inside
  have geo := (Path.segment x.val y.val).isGeodesic_of_lipschitz (Path.segment_lipschitz _ _)
  have restricted := geo.codRestrict (segment ℝ x.val y.val)
    (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
    (fun t => lineMap_mem_segment ℝ x.val y.val t.property)
  intro u v
  change edist (f (q u)) (f (q v)) = edist x y * edist u v
  rw [isometry.edist_eq, edist_eq_of_segment inside]
  exact restricted u v

theorem segmentPath_eLength (inside : segment ℝ x.val y.val ⊆ s) :
    (segmentPath inside).eLength = edist x.val y.val :=
  (segmentPath_isGeodesic inside).eLength_eq_edist.trans (edist_eq_of_segment inside)

theorem exists_step_path (x y : PolygonalPoint s) (finite : stepCost x y ≠ ⊤) :
    ∃ p : Path x y, p.eLength ≤ stepCost x y := by
  classical
  by_cases inside : segment ℝ x.val y.val ⊆ s
  · refine ⟨segmentPath inside, ?_⟩
    rw [segmentPath_eLength, stepCost, ite_eq_left inside]
  · exact (finite (by simp only [stepCost, ite_eq_right inside])).elim

theorem exists_route_path (route : Route (PolygonalPoint s) x y)
    (finite : route.length stepCost ≠ ⊤) :
    ∃ p : Path x y, p.eLength ≤ route.length stepCost := by
  induction route with
  | nil a => exact ⟨Path.refl _, by simp only [Path.eLength_refl, Route.length, le_refl]⟩
  | cons a b tail ih =>
    obtain ⟨first_finite, tail_finite⟩ := ENNReal.add_ne_top.mp finite
    obtain ⟨first, first_bound⟩ := exists_step_path a b first_finite
    obtain ⟨rest, rest_bound⟩ := ih tail_finite
    refine ⟨first.trans rest, ?_⟩
    rw [Path.eLength_trans]
    exact add_le_add first_bound rest_bound

theorem exists_path_eLength_lt (x y : PolygonalPoint s) {r : ℝ≥0∞} (less : edist x y < r) :
    ∃ p : Path x y, p.eLength < r := by
  change (⨅ route : Route (PolygonalPoint s) x y, route.length stepCost) < r at less
  obtain ⟨route, short⟩ := iInf_lt_iff.mp less
  obtain ⟨p, bound⟩ := exists_route_path route (ne_top_of_lt short)
  exact ⟨p, bound.trans_lt short⟩

theorem eDistance_eq_edist (x y : PolygonalPoint s) : Path.eDistance x y = edist x y := by
  apply le_antisymm
  · apply le_of_forall_gt
    intro r less
    obtain ⟨p, short⟩ := exists_path_eLength_lt x y less
    exact p.eDistance_le_eLength.trans_lt short
  · exact Path.edist_le_eDistance _ _

end Unfoldings.PolygonalPoint
