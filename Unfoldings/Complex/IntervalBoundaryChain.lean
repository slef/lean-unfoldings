module

public import Unfoldings.Complex.DirectedBoundaryPathReversal
public import Unfoldings.Complex.BoundaryChainTrace
public import Unfoldings.Topology.PositiveIntervalPartition
public import Unfoldings.Metric.PositiveClosedInterval

/-! An embedded interval covered by exact forward banks constructs its actual bank chain. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam} {T : ℝ} (positive : 0 < T)
  {ι : Type*} (ends : ι ↪ C.BoundaryEnd retain)
  (lower upper : ι → Set.Icc (0 : ℝ) T) (forward : ∀ i, lower i < upper i)
  (curve : Set.Icc (0 : ℝ) T → C.Realization retain) (injective : Function.Injective curve)
  (matching : ∀ i u, C.directedBoundaryPath (ends i) u = curve
    (closedNonnegativeIntervalLineMap (lower i).val (upper i).val T
      (lower i).property.1 (forward i).le (upper i).property.2 u))

include matching in
private theorem interval_piece_first (i : ι) :
    C.directedBoundaryPath (ends i) 0 = curve (lower i) := by
  rw [matching]
  apply congrArg curve
  apply Subtype.ext
  simp only [closedNonnegativeIntervalLineMap, nonnegativeIntervalLineMap, Set.Icc.coe_zero,
    zero_mul, add_zero]

include matching in
private theorem interval_piece_last (i : ι) :
    C.directedBoundaryPath (ends i) 1 = curve (upper i) := by
  rw [matching]
  apply congrArg curve
  apply Subtype.ext
  simp only [closedNonnegativeIntervalLineMap, nonnegativeIntervalLineMap, Set.Icc.coe_one,
    one_mul, add_sub_cancel]

include injective matching in
/-- Forward interval pieces cannot use opposite orientations of one actual bank. -/
theorem interval_pieces_ne_turn (i j : ι) : ends i ≠ C.boundaryTurn retain (ends j) := by
  intro same
  have reverse_first : C.directedBoundaryPath (ends i) 0 = C.directedBoundaryPath (ends j) 1 := by
    rw [same, C.directedBoundaryPath_turn, unitInterval.symm_zero]
  have reverse_last : C.directedBoundaryPath (ends i) 1 = C.directedBoundaryPath (ends j) 0 := by
    rw [same, C.directedBoundaryPath_turn, unitInterval.symm_one]
  have first := injective
    ((C.interval_piece_first ends lower upper forward curve matching i).symm.trans
      (reverse_first.trans (C.interval_piece_last ends lower upper forward curve matching j)))
  have last := injective
    ((C.interval_piece_last ends lower upper forward curve matching i).symm.trans
      (reverse_last.trans (C.interval_piece_first ends lower upper forward curve matching j)))
  have wrong := forward i
  rw [first, last] at wrong
  exact (not_lt_of_ge (forward j).le) wrong

include injective matching in
/-- Distinct original forward bank pieces have disjoint open parameter intervals. -/
theorem interval_pieces_separated : Pairwise (fun i j =>
    Disjoint (Set.Ioo (lower i) (upper i)) (Set.Ioo (lower j) (upper j))) := by
  intro i j different
  apply Set.disjoint_left.mpr
  intro t first last
  have parameter (k : ι) (between : t ∈ Set.Ioo (lower k) (upper k)) :
      ∃ u : unitInterval, 0 < u.val ∧ u.val < 1 ∧
        closedNonnegativeIntervalLineMap (lower k).val (upper k).val T
          (lower k).property.1 (forward k).le (upper k).property.2 u = t := by
    have covered : t ∈ Set.range (closedNonnegativeIntervalLineMap (lower k).val (upper k).val T
        (lower k).property.1 (forward k).le (upper k).property.2) := by
      rw [range_closedNonnegativeIntervalLineMap _ _ _ _ (forward k) _]
      exact ⟨between.1.le, between.2.le⟩
    obtain ⟨u, same⟩ := covered
    have value : (lower k).val + u.val * ((upper k).val - (lower k).val) = t.val :=
      congrArg Subtype.val same
    have lo : (lower k).val < t.val := between.1
    have hi : t.val < (upper k).val := between.2
    have increasing : (lower k).val < (upper k).val := forward k
    exact ⟨u, by nlinarith [u.property.1], by nlinarith [u.property.2], same⟩
  obtain ⟨s, spos, small, at_s⟩ := parameter i first
  obtain ⟨z, _, _, at_z⟩ := parameter j last
  have same : C.directedBoundaryPath (ends i) s = C.directedBoundaryPath (ends j) z := by
    rw [matching, matching, at_s, at_z]
  have bank_equal : (C.boundaryEndEquiv retain (ends i)).1 =
      (C.boundaryEndEquiv retain (ends j)).1 := by
    by_contra apart
    exact C.bankMap_ne_of_ne retain apart
      (C.bankParameterFromEnd _ _ s) (C.bankParameterFromEnd _ _ z)
      (C.bankParameterFromEnd_nonvertex _ _ s spos small) same
  rcases (C.boundaryEnd_bank_eq_iff retain _ _).mp bank_equal with equal | opposite
  · exact different (ends.injective equal)
  · exact C.interval_pieces_ne_turn ends lower upper forward curve injective matching i j opposite

variable [Finite ι]

include injective matching in
/-- Exact forward coverage constructs the whole intrinsic boundary chain. Every original
bank occurs once and every join is the actual successor, without a supplied fan certificate. -/
theorem exists_boundaryChain_of_interval_pieces
    (cover : Set.range curve = ⋃ i, Set.range (C.directedBoundaryPath (ends i))) :
    ∃ n : ℕ, ∃ chain : (C.boundarySystem retain).Chain n, ∃ index : Fin (n + 1) ≃ ι,
      (∀ i, chain.point i = ends (index i)) ∧ Set.range curve = C.boundaryChainTrace chain ∧
      C.vertexPoint retain (C.boundaryEndVertex retain chain.first) =
        curve ⟨0, le_rfl, positive.le⟩ ∧
      C.vertexPoint retain (C.boundaryEndVertex retain (C.boundaryTurn retain chain.last)) =
        curve ⟨T, positive.le, le_rfl⟩ := by
  have covered (t : Set.Icc (0 : ℝ) T) : ∃ i, lower i ≤ t ∧ t ≤ upper i := by
    obtain ⟨i, u, same⟩ := Set.mem_iUnion.mp (cover.subset ⟨t, rfl⟩)
    have at_t := injective ((matching i u).symm.trans same)
    have member : t ∈ Set.range (closedNonnegativeIntervalLineMap (lower i).val (upper i).val T
        (lower i).property.1 (forward i).le (upper i).property.2) := ⟨u, at_t⟩
    rw [range_closedNonnegativeIntervalLineMap _ _ _ _ (forward i) _] at member
    exact ⟨i, member⟩
  obtain ⟨n, index, _, initial, terminal, joins⟩ := exists_ordered_positive_Icc_partition positive
    lower upper forward
    (C.interval_pieces_separated ends lower upper forward curve injective matching) covered
  have apart := C.interval_pieces_ne_turn ends lower upper forward curve injective matching
  have next (i : Fin n) : C.boundaryMate retain (C.boundaryTurn retain (ends (index i.castSucc))) =
      ends (index i.succ) := by
    have endpoints : C.directedBoundaryPath (ends (index i.castSucc)) 1 =
        C.directedBoundaryPath (ends (index i.succ)) 0 := by
      rw [C.interval_piece_last ends lower upper forward curve matching,
        C.interval_piece_first ends lower upper forward curve matching, joins]
    rw [C.directedBoundaryPath_one, C.directedBoundaryPath_zero] at endpoints
    have vertices := C.vertexPoint_injective retain endpoints
    rcases (C.boundaryEnd_vertex_eq_iff retain _ _).mp vertices with equal | paired
    · exact (apart (index i.succ) (index i.castSucc) equal.symm).elim
    · rw [paired, C.boundaryMate_involutive]
  let chain : (C.boundarySystem retain).Chain n := {
    point i := ends (index i)
    injective := ends.injective.comp index.injective
    disjoint i j := apart (index i) (index j)
    next := next }
  refine ⟨n, chain, index, fun _ => rfl, ?_, ?_, ?_⟩
  · rw [C.boundaryChainTrace_eq_union_paths, cover]
    apply Set.ext
    intro x
    constructor
    · rintro member
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
      exact Set.mem_iUnion.mpr ⟨index.symm i,
        by simpa only [chain, index.apply_symm_apply] using hi⟩
    · rintro member
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
      exact Set.mem_iUnion.mpr ⟨index i, hi⟩
  · have first := C.interval_piece_first ends lower upper forward curve matching (index 0)
    rw [C.directedBoundaryPath_zero] at first
    exact first.trans (congrArg curve (Subtype.ext initial))
  · have last := C.interval_piece_last ends lower upper forward curve matching (index (Fin.last n))
    rw [C.directedBoundaryPath_one] at last
    exact last.trans (congrArg curve (Subtype.ext terminal))

end Unfoldings.TriangleComplex
