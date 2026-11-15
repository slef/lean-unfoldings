module

public import Unfoldings.Geometry.RadialNormProgress
public import Unfoldings.Geometry.BankRadialOrder
public import Unfoldings.Geometry.ChainSplit

/-! Quantitative norm progress between every pair of actual polygonal bank points. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n) (source : E) {γ : ℝ} (nonnegative : 0 ≤ γ) (small : γ ≤ 1)
  (margin : ∀ i, γ * (‖P.vertex i.castSucc - source‖ * ‖P.edge i‖) ≤
    inner ℝ (P.vertex i.castSucc - source) (P.edge i))

include small margin in
theorem radial_edge_norm_progress (i : Fin n) :
    γ * ‖P.edge i‖ ≤ ‖P.vertex i.succ - source‖ - ‖P.vertex i.castSucc - source‖ := by
  have step := norm_add_sub_norm_ge_radial_margin
    (P.vertex i.castSucc - source) (P.edge i) small (margin i)
  have equal : P.vertex i.castSucc - source + P.edge i = P.vertex i.succ - source := by
    rw [edge]
    abel
  rwa [equal] at step

include nonnegative small margin in
/-- The estimate follows the whole finite chain, with no comparison point supplied externally. -/
theorem radial_vertex_norm_progress (u v : Fin (n + 1)) (ordered : u ≤ v) :
    γ * ‖P.vertex v - P.vertex u‖ ≤ ‖P.vertex v - source‖ - ‖P.vertex u - source‖ := by
  induction v using Fin.induction generalizing u with
  | zero =>
    have same : u = 0 := le_antisymm ordered (Fin.zero_le _)
    simp [same]
  | succ v ih =>
    by_cases before : u ≤ v.castSucc
    · apply radial_progress_trans source (P.vertex u) (P.vertex v.castSucc) (P.vertex v.succ)
        nonnegative (ih u before)
      simpa only [edge] using P.radial_edge_norm_progress source small margin v
    · have same : u = v.succ := by
        apply Fin.ext
        have after := lt_of_not_ge before
        change v.val < u.val at after
        change u.val ≤ v.val + 1 at ordered
        change u.val = v.val + 1
        omega
      simp [same]

include nonnegative small margin in
/-- Each partial original edge satisfies the same quantitative radial estimate. -/
theorem radial_point_norm_progress (i : Fin n) (t s : unitInterval) (ordered : t ≤ s) :
    γ * ‖P.point i s - P.point i t‖ ≤ ‖P.point i s - source‖ - ‖P.point i t - source‖ := by
  have progress := norm_ray_progress (P.vertex i.castSucc - source) (P.edge i)
    nonnegative small t.property.1 ordered (margin i)
  have relative_point (r : unitInterval) : P.point i r - source =
      (P.vertex i.castSucc - source) + (r : ℝ) • P.edge i := by
    simp only [point, edge, AffineMap.lineMap_apply_module']
    module
  have difference : P.point i s - P.point i t = ((s : ℝ) - (t : ℝ)) • P.edge i := by
    simp only [point, edge, AffineMap.lineMap_apply_module']
    module
  rwa [← relative_point s, ← relative_point t, ← difference] at progress

include nonnegative small margin in
theorem radial_vertex_point_progress (u : Fin (n + 1)) (i : Fin n) (t : unitInterval)
    (before : u ≤ i.castSucc) :
    γ * ‖P.point i t - P.vertex u‖ ≤ ‖P.point i t - source‖ - ‖P.vertex u - source‖ := by
  apply radial_progress_trans source (P.vertex u) (P.vertex i.castSucc) (P.point i t)
    nonnegative (P.radial_vertex_norm_progress source nonnegative small margin u i.castSucc before)
  simpa only [P.point_zero] using
    P.radial_point_norm_progress source nonnegative small margin i 0 t t.property.1

include nonnegative small margin in
theorem radial_point_vertex_progress (i : Fin n) (t : unitInterval) (v : Fin (n + 1))
    (before : i.succ ≤ v) :
    γ * ‖P.vertex v - P.point i t‖ ≤ ‖P.vertex v - source‖ - ‖P.point i t - source‖ := by
  apply radial_progress_trans source (P.point i t) (P.vertex i.succ) (P.vertex v) nonnegative
    (by simpa only [P.point_one] using
      P.radial_point_norm_progress source nonnegative small margin i t 1 t.property.2)
  exact P.radial_vertex_norm_progress source nonnegative small margin i.succ v before

include nonnegative small margin in
/-- Ordered contacts on different original edges retain the same margin. -/
theorem radial_points_norm_progress (i j : Fin n) (t s : unitInterval) (before : Before i t j s) :
    γ * ‖P.point j s - P.point i t‖ ≤ ‖P.point j s - source‖ - ‖P.point i t - source‖ := by
  rcases before with earlier | ⟨rfl, ordered⟩
  · apply radial_progress_trans source (P.point i t) (P.vertex j.castSucc) (P.point j s)
      nonnegative
      (P.radial_point_vertex_progress source nonnegative small margin i t j.castSucc
        (by change i.val + 1 ≤ j.val; exact earlier))
    simpa only [P.point_zero] using
      P.radial_point_norm_progress source nonnegative small margin j 0 s s.property.1
  · exact P.radial_point_norm_progress source nonnegative small margin i t s ordered

include nonnegative small margin in
theorem radial_path_last_progress {x : E} (member : x ∈ Set.range P.path) :
    γ * ‖P.vertex (Fin.last n) - x‖ ≤ ‖P.vertex (Fin.last n) - source‖ - ‖x - source‖ := by
  have cover := P.path_range.subset member
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at cover
  rcases cover with initial | ⟨i, t, rfl⟩
  · rw [Set.mem_singleton_iff.mp initial]
    exact P.radial_vertex_norm_progress source nonnegative small margin 0 (Fin.last n)
      (Fin.zero_le _)
  · exact P.radial_point_vertex_progress source nonnegative small margin i t (Fin.last n)
      (Fin.le_last _)

include nonnegative small margin in
/-- Radius has a quantitative inverse on the entire actual path carrier, including flat edges. -/
theorem radial_path_inverse_bound {x y : E} (first : x ∈ Set.range P.path)
    (last : y ∈ Set.range P.path) : γ * ‖y - x‖ ≤ |‖y - source‖ - ‖x - source‖| := by
  have first_cover := P.path_range.subset first
  have last_cover := P.path_range.subset last
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at first_cover last_cover
  rcases first_cover with initial | ⟨i, t, rfl⟩
  · rw [Set.mem_singleton_iff.mp initial]
    rcases last_cover with last_initial | ⟨j, s, rfl⟩
    · simp [Set.mem_singleton_iff.mp last_initial]
    · exact (P.radial_vertex_point_progress source nonnegative small margin 0 j s
        (Fin.zero_le _)).trans (le_abs_self _)
  · rcases last_cover with initial | ⟨j, s, rfl⟩
    · rw [Set.mem_singleton_iff.mp initial]
      have bound := (P.radial_vertex_point_progress source nonnegative small margin 0 i t
        (Fin.zero_le _)).trans (le_abs_self _)
      simpa only [norm_sub_rev, abs_sub_comm] using bound
    · rcases before_total i j t s with before | before
      · exact (P.radial_points_norm_progress source nonnegative small margin i j t s before).trans
          (le_abs_self _)
      · have bound :=
          (P.radial_points_norm_progress source nonnegative small margin j i s t before).trans
            (le_abs_self _)
        simpa only [norm_sub_rev, abs_sub_comm] using bound

end Unfoldings.PolygonalChain
