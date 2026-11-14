module

public import Unfoldings.Geometry.PolygonalRaySuffix
public import Unfoldings.Geometry.PolygonalRayEmbedding

/-! Source-radius ordering separates the kept prefix from its actual infinite suffix. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (R : PolygonalRay E n)

theorem prefix_radius_le_hinge (outward : R.Outward) (hinge : Fin (n + 1)) {z : E}
    (member : z ∈ Set.range (R.chain.interval 0 hinge.val (by omega)).path) :
    dist R.start z ≤ dist R.start (R.chain.vertex hinge) := by
  have cover := (R.chain.interval 0 hinge.val (by omega)).path_range.subset member
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at cover
  rcases cover with root | ⟨i, t, rfl⟩
  · rw [Set.mem_singleton_iff.mp root]
    change dist R.start R.start ≤ _
    rw [dist_self]
    exact dist_nonneg
  · rw [R.chain.interval_point]
    let j : Fin n := ⟨0 + i.val, by omega⟩
    have edge := outward.1 j (Nat.zero_le _) (show t ≤ (1 : unitInterval) from t.property.2)
    change dist R.start (R.chain.point j t) ≤ dist R.start (R.chain.point j 1) at edge
    rw [R.chain.point_one] at edge
    exact edge.trans (PolygonalChain.RadialFrom.dist_vertices_le R.chain outward.1
      j.succ hinge (Fin.zero_le _) (by change 0 + i.val + 1 ≤ hinge.val; omega))

theorem suffix_radius_ge_hinge (outward : R.Outward) (hinge : Fin (n + 1)) {z : E}
    (member : z ∈ (R.suffix hinge).carrier) :
    dist R.start (R.chain.vertex hinge) ≤ dist R.start z := by
  have vertices := PolygonalChain.RadialFrom.dist_vertices_le R.chain outward.1
  rcases member with finite | ⟨t, rfl⟩
  · have cover := (R.suffix hinge).chain.path_range.subset finite
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at cover
    rcases cover with root | ⟨i, t, rfl⟩
    · rw [Set.mem_singleton_iff.mp root]
      exact le_rfl
    · change _ ≤ dist R.start ((R.chain.interval hinge.val (n - hinge.val) (by omega)).point i t)
      rw [R.chain.interval_point]
      let j : Fin n := ⟨hinge.val + i.val, by omega⟩
      have edge := outward.1 j (Nat.zero_le _) (show (0 : unitInterval) ≤ t from t.property.1)
      change dist R.start (R.chain.point j 0) ≤ dist R.start (R.chain.point j t) at edge
      rw [R.chain.point_zero] at edge
      exact (vertices hinge j.castSucc (Fin.zero_le _)
        (by change hinge.val ≤ hinge.val + i.val; omega)).trans edge
  · rw [R.suffix_tail]
    have last := vertices hinge (Fin.last n) (Fin.zero_le _) (Fin.le_last _)
    have tail := dist_lineMap_le_of_inner_nonneg R.start (R.chain.vertex (Fin.last n))
      (R.chain.vertex (Fin.last n) + R.direction)
      (by simpa only [add_sub_cancel_left] using outward.2) (le_refl 0) t.coe_nonneg
    rw [AffineMap.lineMap_apply_zero, ← R.tail_lineMap] at tail
    exact last.trans tail

/-- A split shares exactly its hinge as an actual point, allowing flat subdivision edges. -/
theorem prefix_suffix_inter (outward : R.Outward) (nonzero : R.direction ≠ 0)
    (hinge : Fin (n + 1)) :
    Set.range (R.chain.interval 0 hinge.val (by omega)).path ∩ (R.suffix hinge).carrier =
      {R.chain.vertex hinge} := by
  ext z
  constructor
  · rintro ⟨kept, future⟩
    have radius := le_antisymm (R.prefix_radius_le_hinge outward hinge kept)
      (R.suffix_radius_ge_hinge outward hinge future)
    exact R.eq_of_radius_eq outward nonzero
      (Or.inl (R.chain.interval_path_range_subset _ _ _ kept))
      (Or.inl (R.chain.vertex_mem_path_range hinge)) radius
  · rintro rfl
    refine ⟨?_, (R.suffix hinge).start_mem⟩
    have endpoint := (R.chain.interval 0 hinge.val (by omega)).vertex_mem_path_range (Fin.last _)
    simpa only [PolygonalChain.interval_last, Nat.zero_add, Fin.eta] using endpoint

end Unfoldings.PolygonalRay
