module

public import Unfoldings.Geometry.ChainLinearGraph
public import Unfoldings.Geometry.PolygonalBankTailGerm
public import Mathlib.Analysis.Complex.Basic

/-! Successive cross-row edges sweep a flat parameter strip without uncovered slices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

variable {n : ℕ} (lower upper : Fin (n + 1) → ℝ)

/-- Longitude of a cross-row edge at normalized latitude `t`. -/
def crossRowLongitude (i : Fin (n + 1)) (t : ℝ) : ℝ :=
  (1 - t) * lower i + t * upper i

/-- The closed region between consecutive cross-row edges. One row advances
and the other is fixed in each actual parameter triangle. -/
def betweenCrossRows (i : Fin n) : Set ℂ :=
  {z | z.im ∈ Set.Icc (0 : ℝ) 1 ∧
    z.re ∈ Set.Icc (crossRowLongitude lower upper i.castSucc z.im)
      (crossRowLongitude lower upper i.succ z.im)}

theorem crossRowLongitude_mono (lo : Monotone lower) (hi : Monotone upper)
    {t : ℝ} (height : t ∈ Set.Icc (0 : ℝ) 1) :
    Monotone fun i => crossRowLongitude lower upper i t := by
  intro i j ordered
  unfold crossRowLongitude
  exact add_le_add (mul_le_mul_of_nonneg_left (lo ordered) (sub_nonneg.mpr height.2))
    (mul_le_mul_of_nonneg_left (hi ordered) height.1)

private theorem iUnion_adjacent_Icc (x : Fin (n + 1) → ℝ) (nonempty : 0 < n) (mono : Monotone x) :
    (⋃ i : Fin n, Set.Icc (x i.castSucc) (x i.succ)) = Set.Icc (x 0) (x (Fin.last n)) := by
  let P : PolygonalChain ℝ n := ⟨x⟩
  let idₗ := ContinuousLinearMap.id ℝ ℝ
  have nonnegative (i : Fin n) : 0 ≤ idₗ (P.edge i) :=
    sub_nonneg.mpr (mono (Fin.castSucc_le_succ _))
  have range : Set.range P.path = Set.Icc (x 0) (x (Fin.last n)) := P.path_linear_range idₗ nonnegative
  rw [← range, P.path_range_eq_segments]
  have contains : {P.vertex 0} ⊆ ⋃ i : Fin n, segment ℝ (P.vertex i.castSucc) (P.vertex i.succ) := by
    rw [Set.singleton_subset_iff]
    exact Set.mem_iUnion.mpr ⟨⟨0, nonempty⟩, left_mem_segment ℝ _ _⟩
  rw [Set.union_eq_right.mpr contains]
  apply Set.iUnion_congr
  intro i
  exact (segment_eq_Icc (mono (Fin.castSucc_le_succ i))).symm

/-- A sweep with fixed common start and end longitudes covers the entire flat strip. -/
theorem iUnion_betweenCrossRows (lo : Monotone lower) (hi : Monotone upper)
    (nonempty : 0 < n) (start finish : ℝ) (lo_start : lower 0 = start)
    (hi_start : upper 0 = start) (lo_end : lower (Fin.last n) = finish)
    (hi_end : upper (Fin.last n) = finish) :
    (⋃ i, betweenCrossRows lower upper i) =
      {z : ℂ | z.im ∈ Set.Icc (0 : ℝ) 1 ∧ z.re ∈ Set.Icc start finish} := by
  ext z
  by_cases height : z.im ∈ Set.Icc (0 : ℝ) 1
  · have start_eq : crossRowLongitude lower upper 0 z.im = start := by
      unfold crossRowLongitude
      rw [lo_start, hi_start]
      ring
    have end_eq : crossRowLongitude lower upper (Fin.last n) z.im = finish := by
      unfold crossRowLongitude
      rw [lo_end, hi_end]
      ring
    simp only [betweenCrossRows, Set.mem_iUnion, Set.mem_ofPred_eq, height, true_and]
    rw [← Set.mem_iUnion, iUnion_adjacent_Icc _ nonempty
      (crossRowLongitude_mono lower upper lo hi height), start_eq, end_eq]
  · constructor
    · intro member
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
      exact (height hi.1).elim
    · intro hz
      exact (height hz.1).elim

/-- An interior point lies strictly between the cross-row edges on its latitude. -/
theorem betweenCrossRows_interior_longitude {i : Fin n} {z : ℂ}
    (member : z ∈ interior (betweenCrossRows lower upper i)) :
    crossRowLongitude lower upper i.castSucc z.im < z.re ∧
      z.re < crossRowLongitude lower upper i.succ z.im := by
  obtain ⟨r, positive, ball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp member)
  let t : ℝ := r / 2
  have left : z - (t : ℂ) ∈ betweenCrossRows lower upper i := by
    apply ball
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ t)]
    dsimp only [t]
    linarith only [positive]
  have right : z + (t : ℂ) ∈ betweenCrossRows lower upper i := by
    apply ball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ t)]
    dsimp only [t]
    linarith only [positive]
  have left_bound := left.2.1
  have right_bound := right.2.2
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.sub_re, Complex.ofReal_re]
    at left_bound
  simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.add_re, Complex.ofReal_re]
    at right_bound
  have half : 0 < t := div_pos positive (by norm_num)
  constructor <;> linarith only [left_bound, right_bound, half]

/-- Every two parameter cells have disjoint interiors. -/
theorem pairwiseDisjoint_betweenCrossRows (lo : Monotone lower) (hi : Monotone upper) :
    Pairwise fun i j => Disjoint (interior (betweenCrossRows lower upper i))
      (interior (betweenCrossRows lower upper j)) := by
  intro i j different
  rw [Set.disjoint_left]
  intro z zi zj
  have height := (interior_subset zi).1
  have mono := crossRowLongitude_mono lower upper lo hi height
  obtain ⟨first, last⟩ := betweenCrossRows_interior_longitude lower upper zi
  obtain ⟨next, finish⟩ := betweenCrossRows_interior_longitude lower upper zj
  rcases lt_or_gt_of_ne different with ij | ji
  · have order : i.succ ≤ j.castSucc := ij
    exact (last.trans_le (mono order)).not_gt next
  · have order : j.succ ≤ i.castSucc := ji
    exact (finish.trans_le (mono order)).not_gt first

end Unfoldings.FewestNets
