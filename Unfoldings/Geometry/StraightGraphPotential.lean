module

public import Unfoldings.Geometry.OrientedSubsegments
public import Mathlib.Tactic.Linarith

/-! Extend vertex ranks affinely along directed embedded edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FiniteEmbeddedGraph

variable {V E X : Type*} [TopologicalSpace X]
  (G : FiniteEmbeddedGraph V E X) (rank : V → ℝ)

open Classical in
/-- The value on the graph is unambiguous because open edges avoid all
vertices and one another. Its arbitrary values off the graph are unused. -/
def interpolatedRank (x : X) : ℝ :=
  if hv : ∃ v, G.vertex v = x then rank hv.choose
  else if he : ∃ e, ∃ t : unitInterval, 0 < t ∧ t < 1 ∧ G.edge e t = x then
    let t := (he.choose_spec.choose : ℝ)
    (1 - t) * rank (G.left he.choose) + t * rank (G.right he.choose)
  else 0

theorem interpolatedRank_vertex (v : V) :
    G.interpolatedRank rank (G.vertex v) = rank v := by
  classical
  have hv : ∃ w, G.vertex w = G.vertex v := ⟨v, rfl⟩
  rw [interpolatedRank, dite_eq_left hv]
  exact congrArg rank (G.vertex_injective hv.choose_spec)

theorem interpolatedRank_edge (e : E) (t : unitInterval) :
    G.interpolatedRank rank (G.edge e t) =
      (1 - (t : ℝ)) * rank (G.left e) + (t : ℝ) * rank (G.right e) := by
  classical
  by_cases zero : t = 0
  · subst t
    rw [G.edge_zero]
    simp [G.interpolatedRank_vertex]
  by_cases one : t = 1
  · subst t
    rw [G.edge_one]
    simp [G.interpolatedRank_vertex]
  have positive : 0 < t := lt_of_le_of_ne unitInterval.nonneg' (Ne.symm zero)
  have before : t < 1 := lt_of_le_of_ne (unitInterval.le_one t) one
  have no_vertex : ¬ ∃ v, G.vertex v = G.edge e t := by
    rintro ⟨v, equal⟩
    exact G.edge_avoids_vertices e t positive before v equal.symm
  have he : ∃ f, ∃ s : unitInterval, 0 < s ∧ s < 1 ∧ G.edge f s = G.edge e t :=
    ⟨e, t, positive, before, rfl⟩
  rw [interpolatedRank, dite_eq_right no_vertex, dite_eq_left he]
  let f := he.choose
  let s := he.choose_spec.choose
  have located := he.choose_spec.choose_spec
  change 0 < s ∧ s < 1 ∧ G.edge f s = G.edge e t at located
  have same_edge : f = e := by
    by_contra different
    have v : G.edge e t ∈ G.edge f '' Set.Ioo (0 : unitInterval) 1 :=
      ⟨s, ⟨located.1, located.2.1⟩, located.2.2⟩
    have w : G.edge e t ∈ G.edge e '' Set.Ioo (0 : unitInterval) 1 :=
      ⟨t, ⟨positive, before⟩, rfl⟩
    exact Set.disjoint_left.mp (G.disjoint_open_edges f e different) v w
  have same_time : s = t := by
    apply G.edge_injective e ⟨located.1, located.2.1⟩ ⟨positive, before⟩
    rw [← same_edge]
    exact located.2.2.trans (congrArg (fun j => G.edge j t) same_edge).symm
  change (1 - (s : ℝ)) * rank (G.left f) + (s : ℝ) * rank (G.right f) = _
  rw [same_edge, same_time]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {G : FiniteEmbeddedGraph V E X} {rank : V → ℝ}

theorem IsStraight.interpolatedRank_strict (straight : G.IsStraight) (e : E)
    (ascent : rank (G.left e) < rank (G.right e)) :
    StrictMonoOn (fun t : ℝ => G.interpolatedRank rank
      (AffineMap.lineMap (G.vertex (G.left e)) (G.vertex (G.right e)) t)) (Set.Icc 0 1) := by
  intro s hs t ht before
  let u : unitInterval := ⟨s, hs⟩
  let v : unitInterval := ⟨t, ht⟩
  have first := G.interpolatedRank_edge rank e u
  have last := G.interpolatedRank_edge rank e v
  rw [straight e u] at first
  rw [straight e v] at last
  change G.interpolatedRank rank
    (AffineMap.lineMap (G.vertex (G.left e)) (G.vertex (G.right e)) s) = _ at first
  change G.interpolatedRank rank
    (AffineMap.lineMap (G.vertex (G.left e)) (G.vertex (G.right e)) t) = _ at last
  dsimp only at first last ⊢
  rw [first, last]
  nlinarith only [mul_pos (sub_pos.mpr before) (sub_pos.mpr ascent)]

/-- The local forward direction on a coarse edge strictly increases its
interpolated rank. The same affine parameters certify the fine subedge. -/
theorem IsStraight.exists_orientedSubsegment_of_forward (straight : G.IsStraight)
    (e : E) {x y : X}
    (start : x ∈ segment ℝ (G.vertex (G.left e)) (G.vertex (G.right e)))
    (nonterminal : x ≠ G.vertex (G.right e))
    (finish : y ∈ segment ℝ x (G.vertex (G.right e))) (different : y ≠ x) :
    ∃ S : G.OrientedSubsegment x y, S.edge = e := by
  let a := G.vertex (G.left e)
  let b := G.vertex (G.right e)
  let L : ℝ →ᵃ[ℝ] X := AffineMap.lineMap a b
  obtain ⟨s, hs, at_x⟩ := (segment_eq_image_lineMap ℝ a b).subset start
  obtain ⟨u, hu, at_y⟩ := (segment_eq_image_lineMap ℝ x b).subset finish
  have before : s < 1 := lt_of_le_of_ne hs.2 (fun h =>
    nonterminal (at_x.symm.trans (h ▸ AffineMap.lineMap_apply_one a b)))
  have advance : 0 < u := lt_of_le_of_ne hu.1 (fun h =>
    different (at_y.symm.trans (h ▸ AffineMap.lineMap_apply_zero x b)))
  let t : ℝ := AffineMap.lineMap s 1 u
  have time_eq : t = s + (1 - s) * u := by
    rw [show t = AffineMap.lineMap s 1 u from rfl, AffineMap.lineMap_apply_ring]
    ring
  have order : s < t := by
    rw [time_eq]
    exact lt_add_of_pos_right _ (mul_pos (sub_pos.mpr before) advance)
  have t_in : t ∈ Set.Icc 0 1 := by
    refine ⟨hs.1.trans order.le, ?_⟩
    rw [time_eq]
    have upper := mul_le_mul_of_nonneg_left hu.2 (sub_nonneg.mpr hs.2)
    linarith only [upper]
  have equation : L t = y := by
    rw [show t = AffineMap.lineMap s 1 u from rfl, L.apply_lineMap]
    change AffineMap.lineMap (AffineMap.lineMap a b s) (AffineMap.lineMap a b 1) u = _
    rwa [at_x, AffineMap.lineMap_apply_one]
  exact ⟨⟨e, s, t, hs, t_in, order, at_x, equation⟩, rfl⟩

theorem IsStraight.rank_lt_of_orientedSubsegment (straight : G.IsStraight) {x y : X}
    (S : G.OrientedSubsegment x y) (ascent : rank (G.left S.edge) < rank (G.right S.edge)) :
    G.interpolatedRank rank x < G.interpolatedRank rank y := by
  have h := straight.interpolatedRank_strict S.edge ascent S.first_mem S.last_mem S.increasing
  simpa only [S.at_first, S.at_last] using h

end Unfoldings.FiniteEmbeddedGraph
