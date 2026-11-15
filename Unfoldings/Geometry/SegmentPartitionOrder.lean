module

public import Unfoldings.Topology.FiniteIntervalPartition
public import Unfoldings.Geometry.SegmentVertices
public import Unfoldings.Geometry.PolygonalChain

/-! A genuine segment subdivision has an ordered chain using every actual piece once. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuine segment's affine parameter, with its actual endpoint bounds. -/
def segmentParameter {a b : E} (different : a ≠ b) (p : segment ℝ a b) : unitInterval :=
  ⟨lineCoordinate a b p.val, by
    obtain ⟨t, bounds, equal⟩ := (segment_eq_image_lineMap ℝ a b).subset p.property
    rw [← equal, lineCoordinate_lineMap different]
    exact bounds⟩

@[simp] theorem segmentParameter_lineMap {a b : E} (different : a ≠ b) (t : unitInterval) :
    segmentParameter different ⟨AffineMap.lineMap a b (t : ℝ),
      lineMap_mem_segment ℝ a b t.property⟩ = t := by
  apply Subtype.ext
  exact lineCoordinate_lineMap different t.val

/-- The chain remembers the actual fine pieces and their endpoint direction; none is repeated. -/
structure OrderedSegmentPartition (a b : E) (first last : ι → E) where
  length : ℕ
  chain : PolygonalChain E (length + 1)
  index : Fin (length + 1) ≃ ι
  start : chain.vertex 0 = a
  finish : chain.vertex (Fin.last (length + 1)) = b
  endpoints : ∀ i, (chain.vertex i.castSucc = first (index i) ∧
      chain.vertex i.succ = last (index i)) ∨
    (chain.vertex i.castSucc = last (index i) ∧ chain.vertex i.succ = first (index i))
  ordered : StrictMono (fun i => lineCoordinate a b (chain.vertex i))

variable [Finite ι]

/-- Geometric coverage and disjoint open fine segments construct the entire directed subdivision. -/
theorem exists_ordered_segment_partition {a b : E} (different : a ≠ b) (first last : ι → E)
    (genuine : ∀ i, first i ≠ last i)
    (inside : ∀ i, segment ℝ (first i) (last i) ⊆ segment ℝ a b)
    (separated : Pairwise (fun i j => Disjoint (openSegment ℝ (first i) (last i))
      (openSegment ℝ (first j) (last j))))
    (cover : segment ℝ a b ⊆ ⋃ i, segment ℝ (first i) (last i)) :
    Nonempty (OrderedSegmentPartition a b first last) := by
  classical
  let start (i : ι) := segmentParameter different
    ⟨first i, inside i (left_mem_segment ℝ _ _)⟩
  let finish (i : ι) := segmentParameter different
    ⟨last i, inside i (right_mem_segment ℝ _ _)⟩
  let lower (i : ι) := min (start i) (finish i)
  let upper (i : ι) := max (start i) (finish i)
  have first_line (i) := segment_subset_line a b (inside i (left_mem_segment ℝ _ _))
  have last_line (i) := segment_subset_line a b (inside i (right_mem_segment ℝ _ _))
  have different_parameters (i : ι) : start i ≠ finish i := by
    intro equal
    exact genuine i (lineCoordinate_injective different (first_line i) (last_line i)
      (congrArg Subtype.val equal))
  have positive (i : ι) : lower i < upper i := min_lt_max.mpr (different_parameters i)
  have closed_parameter (i : ι) (t : unitInterval) :
      AffineMap.lineMap a b (t : ℝ) ∈ segment ℝ (first i) (last i) ↔
        lower i ≤ t ∧ t ≤ upper i := by
    have coordinates := lineCoordinate_mem_segment_iff different (first_line i) (last_line i)
      (segment_subset_line a b (lineMap_mem_segment ℝ a b t.property))
    rw [lineCoordinate_lineMap different] at coordinates
    exact coordinates
  have open_parameter (i : ι) (t : unitInterval) :
      AffineMap.lineMap a b (t : ℝ) ∈ openSegment ℝ (first i) (last i) ↔
        lower i < t ∧ t < upper i := by
    have coordinates := lineCoordinate_mem_openSegment_iff different (genuine i)
      (first_line i) (last_line i)
      (segment_subset_line a b (lineMap_mem_segment ℝ a b t.property))
    rw [lineCoordinate_lineMap different] at coordinates
    exact coordinates
  have disjoint : Pairwise (fun i j => Disjoint (Set.Ioo (lower i) (upper i))
      (Set.Ioo (lower j) (upper j))) := by
    intro i j different
    apply Set.disjoint_left.mpr
    intro t first last
    exact Set.disjoint_left.mp (separated different) ((open_parameter i t).mpr first)
      ((open_parameter j t).mpr last)
  have covered (t : unitInterval) : ∃ i, lower i ≤ t ∧ t ≤ upper i := by
    obtain ⟨i, member⟩ := Set.mem_iUnion.mp (cover (lineMap_mem_segment ℝ a b t.property))
    exact ⟨i, (closed_parameter i t).mp member⟩
  obtain ⟨n, index, strict, initial, terminal, joins⟩ :=
    exists_ordered_interval_partition lower upper positive disjoint covered
  let time : Fin (n + 1 + 1) → unitInterval :=
    Fin.lastCases 1 (fun i => lower (index i))
  have time_first (i : Fin (n + 1)) : time i.castSucc = lower (index i) :=
    Fin.lastCases_castSucc _
  have time_last : time (Fin.last (n + 1)) = 1 := Fin.lastCases_last
  have time_next (i : Fin (n + 1)) : time i.succ = upper (index i) := by
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [Fin.succ_last, time_last, terminal]
    · rw [Fin.succ_castSucc, time_first, joins]
  let chain : PolygonalChain E (n + 1) := ⟨fun i => AffineMap.lineMap a b (time i : ℝ)⟩
  have low (i) : chain.vertex i.castSucc =
      AffineMap.lineMap a b (lower (index i) : ℝ) := by
    change AffineMap.lineMap a b (time i.castSucc : ℝ) = _
    rw [time_first]
  have high (i) : chain.vertex i.succ = AffineMap.lineMap a b (upper (index i) : ℝ) := by
    change AffineMap.lineMap a b (time i.succ : ℝ) = _
    rw [time_next]
  have recover_first (i) : AffineMap.lineMap a b (start i : ℝ) = first i :=
    lineCoordinate_recover different (first_line i)
  have recover_last (i) : AffineMap.lineMap a b (finish i : ℝ) = last i :=
    lineCoordinate_recover different (last_line i)
  refine ⟨⟨n, chain, index, ?_, ?_, ?_, ?_⟩⟩
  · change AffineMap.lineMap a b (time (0 : Fin (n + 1)).castSucc : ℝ) = a
    rw [time_first, initial]
    exact AffineMap.lineMap_apply_zero _ _
  · change AffineMap.lineMap a b (time (Fin.last (n + 1)) : ℝ) = b
    rw [time_last]
    exact AffineMap.lineMap_apply_one _ _
  · intro i
    rw [low, high]
    rcases le_total (start (index i)) (finish (index i)) with first | last
    · left
      simpa only [lower, upper, min_eq_left first, max_eq_right first] using
        And.intro (recover_first (index i)) (recover_last (index i))
    · right
      simpa only [lower, upper, min_eq_right last, max_eq_left last] using
        And.intro (recover_last (index i)) (recover_first (index i))
  · apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    rw [low, high, lineCoordinate_lineMap different, lineCoordinate_lineMap different]
    exact positive (index i)

end Unfoldings
