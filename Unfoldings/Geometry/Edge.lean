module

public import Unfoldings.Geometry.Triangle
public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Tactic.LinearCombination

/-! Closed triangle edges, their intersections, and preservation of endpoints by edge isometries. -/

@[expose] public section

namespace Unfoldings

theorem orient_eq_zero_of_mem_segment {a b x : Plane} (hx : x ∈ segment ℝ a b) :
    orient a b x = 0 := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, _, rfl⟩ := hx
  rw [AffineMap.lineMap_apply_module']
  change (b 0 - a 0) * (t * (b 1 - a 1) + a 1 - a 1) -
    (b 1 - a 1) * (t * (b 0 - a 0) + a 0 - a 0) = 0
  ring

/-- Two nonparallel edge lines meet at their common corner. -/
theorem eq_middle_of_orient_eq_zero {a b c x : Plane} (nondegenerate : orient a b c ≠ 0)
    (left : orient a b x = 0) (right : orient b c x = 0) : x = b := by
  have eq0 : orient a b c * (x 0 - b 0) = 0 := by
    unfold orient at *
    linear_combination (c 0 - b 0) * left - (b 0 - a 0) * right
  have eq1 : orient a b c * (x 1 - b 1) = 0 := by
    unfold orient at *
    linear_combination (c 1 - b 1) * left - (b 1 - a 1) * right
  ext i
  fin_cases i
  · exact sub_eq_zero.mp ((mul_eq_zero.mp eq0).resolve_left nondegenerate)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp eq1).resolve_left nondegenerate)

/-- An isometry of closed Euclidean segments sends either endpoint to an endpoint. -/
theorem segment_isometry_maps_endpoint {a b c d : Plane}
    (f : (segment ℝ a b) ≃ᵢ (segment ℝ c d)) (x : segment ℝ a b)
    (endpoint : x.val = a ∨ x.val = b) : (f x).val = c ∨ (f x).val = d := by
  have main (y : segment ℝ a b)
      (bound : ∀ z : segment ℝ c d, dist z (f y) ≤ dist x y) :
      (f x).val = c ∨ (f x).val = d := by
    by_contra neither
    have strict : Sbtw ℝ c (f x).val d :=
      ⟨mem_segment_iff_wbtw.mp (f x).property,
        fun h => neither (Or.inl h), fun h => neither (Or.inr h)⟩
    have too_far := strict.dist_lt_max_dist (f y).val
    have same : dist (f x).val (f y).val = dist x y := f.isometry.dist_eq x y
    rw [same] at too_far
    exact (lt_irrefl _ (too_far.trans_le
      (max_le (bound ⟨c, left_mem_segment ℝ _ _⟩) (bound ⟨d, right_mem_segment ℝ _ _⟩))))
  rcases endpoint with endpoint | endpoint
  · apply main ⟨b, right_mem_segment ℝ _ _⟩
    intro z
    have bound := (mem_segment_iff_wbtw.mp (f.symm z).property).dist_le_max_dist b
    have same := f.isometry.dist_eq (f.symm z) ⟨b, right_mem_segment ℝ _ _⟩
    rw [f.apply_symm_apply z] at same
    rw [same]
    change dist (f.symm z).val b ≤ dist x.val b
    simpa only [endpoint, dist_self, max_eq_left dist_nonneg] using bound
  · apply main ⟨a, left_mem_segment ℝ _ _⟩
    intro z
    have bound := (mem_segment_iff_wbtw.mp (f.symm z).property).dist_le_max_dist a
    have same := f.isometry.dist_eq (f.symm z) ⟨a, left_mem_segment ℝ _ _⟩
    rw [f.apply_symm_apply z] at same
    rw [same]
    change dist (f.symm z).val a ≤ dist x.val a
    simpa only [endpoint, dist_self, max_eq_right dist_nonneg] using bound

namespace Triangle

/-- Whether a point is one of the three original corners. -/
def IsVertex (T : Triangle) (x : Plane) : Prop := x ∈ Set.range T.vertex

theorem edge_vertex_iff (T : Triangle) (e : Fin 3) (x : T.Edge e) :
    T.IsVertex x ↔ x.val = T.vertex e ∨ x.val = T.vertex (next e) := by
  constructor
  · rintro ⟨i, equal⟩
    rcases corner_cases e i with rfl | rfl | rfl
    · exact Or.inl equal.symm
    · exact Or.inr equal.symm
    · exact (T.orient_edge_ne_zero e (by
        rw [opposite, equal]
        exact orient_eq_zero_of_mem_segment x.property)).elim
  · rintro (equal | equal)
    · exact ⟨e, equal.symm⟩
    · exact ⟨next e, equal.symm⟩

/-- Every nondegenerate edge has an interior point distinct from all triangle corners. -/
theorem exists_edge_nonvertex (T : Triangle) (e : Fin 3) : ∃ x : T.Edge e, ¬ T.IsVertex x := by
  let x : T.Edge e := ⟨midpoint ℝ (T.vertex e) (T.vertex (next e)), midpoint_mem_segment _ _⟩
  refine ⟨x, ?_⟩
  intro vertex
  rcases (T.edge_vertex_iff e x).mp vertex with left | right
  · exact T.edge_endpoints_ne e ((midpoint_eq_left_iff (R := ℝ)).mp left)
  · exact T.edge_endpoints_ne e ((midpoint_eq_right_iff (R := ℝ)).mp right)

theorem eq_vertex_of_mem_edge_of_mem_next (T : Triangle) (e : Fin 3) {x : Plane}
    (he : x ∈ T.edge e) (hn : x ∈ T.edge (next e)) : x = T.vertex (next e) :=
  eq_middle_of_orient_eq_zero (T.orient_edge_ne_zero e)
    (orient_eq_zero_of_mem_segment he) (orient_eq_zero_of_mem_segment hn)

/-- Different local edges of a nondegenerate triangle only meet at corners. -/
theorem isVertex_of_mem_edges (T : Triangle) {e f : Fin 3} (different : e ≠ f) {x : Plane}
    (he : x ∈ T.edge e) (hf : x ∈ T.edge f) : T.IsVertex x := by
  have adjacent : f = next e ∨ e = next f := by
    fin_cases e <;> fin_cases f <;> simp_all [next]
  rcases adjacent with rfl | rfl
  · exact ⟨next e, (T.eq_vertex_of_mem_edge_of_mem_next e he hf).symm⟩
  · exact ⟨next f, (T.eq_vertex_of_mem_edge_of_mem_next f hf he).symm⟩

/-- Edge identifications preserve the distinction between corners and edge interiors. -/
theorem edge_isometry_isVertex_iff (T U : Triangle) (e f : Fin 3)
    (identify : T.Edge e ≃ᵢ U.Edge f) (x : T.Edge e) :
    U.IsVertex (identify x) ↔ T.IsVertex x := by
  constructor
  · intro vertex
    have endpoints := segment_isometry_maps_endpoint identify.symm (identify x)
      ((U.edge_vertex_iff f _).mp vertex)
    have back : T.IsVertex (identify.symm (identify x)).val :=
      (T.edge_vertex_iff e _).mpr endpoints
    exact (identify.symm_apply_apply x) ▸ back
  · intro vertex
    exact (U.edge_vertex_iff f _).mpr
      (segment_isometry_maps_endpoint identify x ((T.edge_vertex_iff e x).mp vertex))

end Triangle
end Unfoldings
