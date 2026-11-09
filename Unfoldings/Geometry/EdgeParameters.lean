module

public import Unfoldings.Geometry.Endpoints

/-! Strict edge interpolation stays away from every original triangle vertex. -/

@[expose] public section

namespace Unfoldings.Triangle

theorem lineMap_edge_not_vertex (T : Triangle) (e : Fin 3) {t : ℝ}
    (inside : t ∈ Set.Ioo (0 : ℝ) 1) :
    ¬ T.IsVertex (AffineMap.lineMap (T.vertex e) (T.vertex (next e)) t) := by
  let p : T.Edge e := ⟨_, lineMap_mem_segment ℝ _ _ ⟨inside.1.le, inside.2.le⟩⟩
  intro vertex
  rcases (T.edge_vertex_iff e p).mp vertex with first | last
  · have parameter : t = 0 := (AffineMap.lineMap_eq_left_iff.mp first).resolve_left
      (T.edge_endpoints_ne e)
    exact inside.1.ne' parameter
  · have parameter : t = 1 := (AffineMap.lineMap_eq_right_iff.mp last).resolve_left
      (T.edge_endpoints_ne e)
    exact inside.2.ne parameter

theorem lineMap_endpoints_mem_edge (T : Triangle) (e : Fin 3) (b : Bool) {t : ℝ}
    (inside : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap (T.endpoint e b).val (T.endpoint e (!b)).val t ∈ T.edge e := by
  cases b
  · exact lineMap_mem_segment ℝ _ _ inside
  · change AffineMap.lineMap (T.vertex (next e)) (T.vertex e) t ∈ _
    rw [← AffineMap.lineMap_apply_one_sub]
    exact lineMap_mem_segment ℝ _ _ ⟨by linarith [inside.2], by linarith [inside.1]⟩

theorem lineMap_endpoints_not_vertex (T : Triangle) (e : Fin 3) (b : Bool) {t : ℝ}
    (inside : t ∈ Set.Ioo (0 : ℝ) 1) :
    ¬ T.IsVertex (AffineMap.lineMap (T.endpoint e b).val (T.endpoint e (!b)).val t) := by
  cases b
  · exact T.lineMap_edge_not_vertex e inside
  · change ¬ T.IsVertex (AffineMap.lineMap (T.vertex (next e)) (T.vertex e) t)
    rw [← AffineMap.lineMap_apply_one_sub]
    exact T.lineMap_edge_not_vertex e ⟨by linarith [inside.2], by linarith [inside.1]⟩

end Unfoldings.Triangle
