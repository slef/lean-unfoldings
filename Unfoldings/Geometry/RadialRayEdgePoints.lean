module

public import Unfoldings.Geometry.RadialVertexCoordinates

/-! Exact incidences and strict progress at points inside original outward bank edges. -/

@[expose] public section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (R : PolygonalRay E n) (outward : R.Outward)
  (genuine : ∀ i : Fin n, R.chain.vertex i.castSucc ≠ R.chain.vertex i.succ)

include outward genuine

/-- Strict original edge interiors do not meet any other original closed edge. -/
theorem point_not_mem_other_segment (i : Fin n) (t : unitInterval) (bounds : 0 < t ∧ t < 1)
    (j : Fin n) (different : j ≠ i) :
    R.chain.point i t ∉ segment ℝ (R.chain.vertex j.castSucc) (R.chain.vertex j.succ) := by
  intro member
  rw [segment_eq_image_lineMap] at member
  obtain ⟨s, sbounds, equal⟩ := member
  let u : unitInterval := ⟨s, sbounds⟩
  have at_u : R.chain.point j u = R.chain.point i t := equal
  rcases lt_or_gt_of_ne different with before | after
  · have ordered : j.succ ≤ i.castSucc := by change j.val + 1 ≤ i.val; exact before
    have left := (R.edge_radius_strictMono outward genuine j).monotone
      (show u ≤ (1 : unitInterval) from u.property.2)
    have middle := (R.vertex_radius_strictMono outward genuine).monotone ordered
    have right := R.edge_radius_strictMono outward genuine i bounds.1
    dsimp only at left right
    rw [R.chain.point_one, at_u] at left
    rw [R.chain.point_zero] at right
    exact (not_lt_of_ge (left.trans middle)) right
  · have ordered : i.succ ≤ j.castSucc := by change i.val + 1 ≤ j.val; exact after
    have left := R.edge_radius_strictMono outward genuine i bounds.2
    have middle := (R.vertex_radius_strictMono outward genuine).monotone ordered
    have right := (R.edge_radius_strictMono outward genuine j).monotone
      (show (0 : unitInterval) ≤ u from u.property.1)
    dsimp only at left right
    rw [R.chain.point_one] at left
    rw [R.chain.point_zero, at_u] at right
    exact (not_lt_of_ge right) (left.trans_le middle)

/-- The strict interior of every original finite edge avoids the whole later tail. -/
theorem point_not_mem_tail (nonzero : R.direction ≠ 0) (i : Fin n) (t : unitInterval)
    (before : t < 1) : R.chain.point i t ∉ Set.range R.tail := by
  rintro ⟨s, equal⟩
  have first := R.edge_radius_strictMono outward genuine i before
  dsimp only at first
  rw [R.chain.point_one] at first
  have middle := (R.vertex_radius_strictMono outward genuine).monotone (Fin.le_last i.succ)
  have last := (R.tail_radius_strictMono outward nonzero).monotone
    (show (0 : ℝ≥0) ≤ s from zero_le)
  rw [R.tail_zero, equal] at last
  exact (not_lt_of_ge last) (first.trans_le middle)

/-- A positive edge parameter is beyond the source even on the original first edge. -/
theorem point_ne_start (i : Fin n) (t : unitInterval) (after : 0 < t) :
    R.chain.point i t ≠ R.start := by
  intro equal
  have first := R.edge_radius_strictMono outward genuine i after
  dsimp only at first
  rw [R.chain.point_zero, equal, dist_self] at first
  exact (not_lt_of_ge dist_nonneg) first

/-- Every strict positive point of a genuine outward edge has strictly positive radial
progress in its original forward direction, even if the initial margin vanishes. -/
theorem inner_edge_point_pos (i : Fin n) (t : unitInterval) (after : 0 < t) :
    0 < inner ℝ (R.chain.point i t - R.start) (R.chain.edge i) := by
  have initial := (monotone_dist_lineMap_iff R.start (R.chain.vertex i.castSucc)
    (R.chain.vertex i.succ)).mp (outward.1 i (Nat.zero_le _))
  have nonzero : R.chain.edge i ≠ 0 := sub_ne_zero.mpr (genuine i).symm
  have positive := mul_pos (show (0 : ℝ) < t from after)
    (sq_pos_of_pos (norm_pos_iff.mpr nonzero))
  have difference : R.chain.point i t - R.start =
      (R.chain.vertex i.castSucc - R.start) + (t : ℝ) • R.chain.edge i := by
    simp only [PolygonalChain.point, AffineMap.lineMap_apply_module', PolygonalChain.edge]
    abel
  rw [difference, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  change 0 ≤ inner ℝ (R.chain.vertex i.castSucc - R.start) (R.chain.edge i) at initial
  linarith

end Unfoldings.PolygonalRay
