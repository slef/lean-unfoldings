module

public import Unfoldings.Geometry.SegmentPartitionOrder

/-! A genuine ordered segment partition preserves length under every affine map. -/

@[expose] public section

noncomputable section

namespace Unfoldings.OrderedSegmentPartition

variable {V W ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype ι]
  {a b : V} {first last : ι → V} (G : OrderedSegmentPartition a b first last)

include G in
/-- The actual pieces have exactly the endpoint distance in every affine coordinate system,
including nonisometric projections. Each piece is counted once in either endpoint order. -/
theorem sum_dist_affine_eq (different : a ≠ b)
    (inside_first : ∀ i, first i ∈ segment ℝ a b)
    (inside_last : ∀ i, last i ∈ segment ℝ a b) (F : V →ᵃ[ℝ] W) :
    (∑ i, dist (F (first i)) (F (last i))) = dist (F a) (F b) := by
  have inside (j : Fin (G.length + 2)) : G.chain.vertex j ∈ segment ℝ a b := by
    refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [G.finish]
      exact right_mem_segment ℝ a b
    · rcases G.endpoints k with pair | pair
      · rw [pair.1]
        exact inside_first _
      · rw [pair.1]
        exact inside_last _
  let t (j : Fin (G.length + 2)) := lineCoordinate a b (G.chain.vertex j)
  have positions (j) : F (G.chain.vertex j) = F a + t j • (F b - F a) := by
    rw [← lineCoordinate_recover different (segment_subset_line a b (inside j)),
      F.apply_lineMap, AffineMap.lineMap_apply_module']
    exact add_comm _ _
  have start : t 0 = 0 := by
    dsimp only [t]
    rw [G.start]
    simpa only [AffineMap.lineMap_apply_zero] using lineCoordinate_lineMap different 0
  have finish : t (Fin.last (G.length + 1)) = 1 := by
    dsimp only [t]
    rw [G.finish]
    simpa only [AffineMap.lineMap_apply_one] using lineCoordinate_lineMap different 1
  have telescoping : (∑ k : Fin (G.length + 1), (t k.succ - t k.castSucc)) = 1 := by
    have same : t 0 + ∑ k : Fin (G.length + 1), t k.succ =
        (∑ k : Fin (G.length + 1), t k.castSucc) + t (Fin.last (G.length + 1)) := by
      rw [← Fin.sum_univ_succ, ← Fin.sum_univ_castSucc]
    rw [Finset.sum_sub_distrib]
    rw [start, finish] at same
    linarith
  have lengths (k : Fin (G.length + 1)) :
      dist (F (G.chain.vertex k.castSucc)) (F (G.chain.vertex k.succ)) =
        (t k.succ - t k.castSucc) * dist (F a) (F b) := by
    have ordered : 0 ≤ t k.succ - t k.castSucc :=
      sub_nonneg.mpr (G.ordered (show k.castSucc < k.succ from Fin.castSucc_lt_succ)).le
    rw [dist_eq_norm', positions, positions]
    have vector : F a + t k.succ • (F b - F a) -
        (F a + t k.castSucc • (F b - F a)) =
          (t k.succ - t k.castSucc) • (F b - F a) := by rw [sub_smul]; abel
    rw [vector, norm_smul, Real.norm_of_nonneg ordered, dist_eq_norm']
  calc
    _ = ∑ k : Fin (G.length + 1), dist (F (first (G.index k))) (F (last (G.index k))) :=
      (Equiv.sum_comp G.index (fun i => dist (F (first i)) (F (last i)))).symm
    _ = ∑ k : Fin (G.length + 1),
        dist (F (G.chain.vertex k.castSucc)) (F (G.chain.vertex k.succ)) := by
      apply Finset.sum_congr rfl
      intro k _
      rcases G.endpoints k with pair | pair
      · rw [pair.1, pair.2]
      · rw [pair.1, pair.2, dist_comm]
    _ = ∑ k : Fin (G.length + 1),
        (t k.succ - t k.castSucc) * dist (F a) (F b) := Finset.sum_congr rfl (fun k _ => lengths k)
    _ = _ := by rw [← Finset.sum_mul, telescoping, one_mul]

end Unfoldings.OrderedSegmentPartition
