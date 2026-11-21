module

public import Unfoldings.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Tactic

/-! The closest distance between disjoint planar segments is realized at an endpoint. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Set

private theorem inner_eq_zero_of_min_affine_norm_sq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x d : E) {t : ℝ}
    (inside : t ∈ Ioo (0 : ℝ) 1)
    (minimum : IsMinOn (fun r : ℝ => ‖x + r • d‖ ^ 2) (Icc 0 1) t) :
    inner ℝ (x + t • d) d = 0 := by
  have min_local : IsLocalMin (fun r : ℝ => ‖x + r • d‖ ^ 2) t :=
    minimum.isLocalMin (Icc_mem_nhds inside.1 inside.2)
  have direction : HasDerivAt (fun r : ℝ => x + r • d) d t := by
    simpa only [one_smul, zero_add, Pi.add_def, id_eq] using
      (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const d)
  have derivative := HasDerivAt.inner ℝ direction direction
  have result := min_local.hasDerivAt_eq_zero (by
    simpa only [real_inner_self_eq_norm_sq] using derivative)
  rw [real_inner_comm (x + t • d) d] at result
  linarith only [result]

private theorem exists_slide_to_parameter_edge {t s : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) (c : ℝ) (ne : c ≠ 0) :
    ∃ u v : ℝ, u ∈ Icc 0 1 ∧ v ∈ Icc 0 1 ∧ (u = 1 ∨ v = 0 ∨ v = 1) ∧
      v = s + c * (u - t) := by
  rcases ne.lt_or_gt with negative | positive
  · let d := min (1 - t) (s / -c)
    have dpos : 0 ≤ d := le_min (sub_nonneg.mpr ht.2.le) (div_nonneg hs.1.le (by linarith))
    have du : d ≤ 1 - t := min_le_left _ _
    have dv : d ≤ s / -c := min_le_right _ _
    have lower : 0 ≤ s + c * d := by
      have mul := (le_div_iff₀ (by linarith : 0 < -c)).mp dv
      linarith only [mul]
    have upper : s + c * d ≤ 1 := by
      linarith only [mul_nonpos_of_nonpos_of_nonneg negative.le dpos, hs.2]
    refine ⟨t + d, s + c * d, ⟨by linarith [ht.1], by linarith⟩, ⟨lower, upper⟩, ?_, by ring⟩
    rcases le_total (1 - t) (s / -c) with h | h
    · left
      dsimp only [d]
      rw [min_eq_left h]
      ring
    · right
      left
      dsimp only [d]
      rw [min_eq_right h]
      field_simp
      ring
  · let d := min (1 - t) ((1 - s) / c)
    have dpos : 0 ≤ d := le_min (sub_nonneg.mpr ht.2.le)
      (div_nonneg (sub_nonneg.mpr hs.2.le) positive.le)
    have du : d ≤ 1 - t := min_le_left _ _
    have dv : d ≤ (1 - s) / c := min_le_right _ _
    have lower : 0 ≤ s + c * d := add_nonneg hs.1.le (mul_nonneg positive.le dpos)
    have upper : s + c * d ≤ 1 := by
      have mul := (le_div_iff₀ positive).mp dv
      linarith only [mul]
    refine ⟨t + d, s + c * d, ⟨by linarith [ht.1], by linarith⟩, ⟨lower, upper⟩, ?_, by ring⟩
    rcases le_total (1 - t) ((1 - s) / c) with h | h
    · left
      dsimp only [d]
      rw [min_eq_left h]
      ring
    · right
      right
      dsimp only [d]
      rw [min_eq_right h]
      field_simp
      ring

set_option maxHeartbeats 1000000 in
-- The compact minimizer, first variation and parallel slide stay in one statement.
/-- Among the closest pairs of points on two disjoint planar segments, one
pair contains at least one endpoint. -/
theorem exists_endpoint_minimizing_segment_dist {a b c d : Plane}
    (disjoint : Disjoint (segment ℝ a b) (segment ℝ c d)) :
    ∃ x ∈ segment ℝ a b, ∃ y ∈ segment ℝ c d,
      (x = a ∨ x = b ∨ y = c ∨ y = d) ∧
        ∀ x' ∈ segment ℝ a b, ∀ y' ∈ segment ℝ c d, dist x y ≤ dist x' y' := by
  let p (r : ℝ) := a + r • (b - a)
  let q (r : ℝ) := c + r • (d - c)
  have p_param (r : ℝ) : p r = AffineMap.lineMap a b r := by
    rw [AffineMap.lineMap_apply_module']
    exact add_comm _ _
  have q_param (r : ℝ) : q r = AffineMap.lineMap c d r := by
    rw [AffineMap.lineMap_apply_module']
    exact add_comm _ _
  have p_mem {r : ℝ} (hr : r ∈ Icc 0 1) : p r ∈ segment ℝ a b := by
    rw [segment_eq_image_lineMap]
    exact ⟨r, hr, (p_param r).symm⟩
  have q_mem {r : ℝ} (hr : r ∈ Icc 0 1) : q r ∈ segment ℝ c d := by
    rw [segment_eq_image_lineMap]
    exact ⟨r, hr, (q_param r).symm⟩
  let I := Icc (0 : ℝ) 1
  let measure (z : ℝ × ℝ) := ‖p z.1 - q z.2‖ ^ 2
  have continuous_measure : Continuous measure := by
    dsimp [measure, p, q]
    fun_prop
  obtain ⟨⟨t, s⟩, member, minimum⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMinOn
    (show (I ×ˢ I).Nonempty from ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩⟩)
    continuous_measure.continuousOn
  have ht : t ∈ I := member.1
  have hs : s ∈ I := member.2
  have minimizer (u v : ℝ) (hu : u ∈ I) (hv : v ∈ I)
      (endpoints : p u = a ∨ p u = b ∨ q v = c ∨ q v = d)
      (eq : measure (u, v) = measure (t, s)) :
      ∃ x ∈ segment ℝ a b, ∃ y ∈ segment ℝ c d,
        (x = a ∨ x = b ∨ y = c ∨ y = d) ∧
          ∀ x' ∈ segment ℝ a b, ∀ y' ∈ segment ℝ c d, dist x y ≤ dist x' y' := by
    refine ⟨p u, p_mem hu, q v, q_mem hv, endpoints, ?_⟩
    intro x hx y hy
    rw [segment_eq_image_lineMap] at hx hy
    obtain ⟨xarg, xarg_mem, xeq⟩ := hx
    obtain ⟨yarg, yarg_mem, yeq⟩ := hy
    have bound := minimum (show (xarg, yarg) ∈ I ×ˢ I from ⟨xarg_mem, yarg_mem⟩)
    rw [← eq] at bound
    change ‖p u - q v‖ ^ 2 ≤ ‖p xarg - q yarg‖ ^ 2 at bound
    rw [p_param xarg, q_param yarg, xeq, yeq] at bound
    rw [dist_eq_norm, dist_eq_norm]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp bound
  by_cases already : p t = a ∨ p t = b ∨ q s = c ∨ q s = d
  · exact minimizer t s ht hs already rfl
  have t_int : t ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩
    · intro zero
      apply already
      exact .inl (by rw [← zero, p_param, AffineMap.lineMap_apply_zero])
    · intro one
      apply already
      exact .inr (.inl (by rw [one, p_param, AffineMap.lineMap_apply_one]))
  have s_int : s ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨lt_of_le_of_ne hs.1 ?_, lt_of_le_of_ne hs.2 ?_⟩
    · intro zero
      apply already
      exact .inr (.inr (.inl (by rw [← zero, q_param, AffineMap.lineMap_apply_zero])))
    · intro one
      apply already
      exact .inr (.inr (.inr (by rw [one, q_param, AffineMap.lineMap_apply_one])))
  let u := b - a
  let v := d - c
  let w := p t - q s
  have w_ne : w ≠ 0 := by
    intro zero
    have eq : p t = q s := sub_eq_zero.mp zero
    exact (Set.disjoint_left.mp disjoint) (p_mem ht) (eq.symm ▸ q_mem hs)
  have u_ne : u ≠ 0 := by
    intro zero
    apply already
    exact .inl (by change a + t • u = a; simp [zero])
  have v_ne : v ≠ 0 := by
    intro zero
    apply already
    exact .inr (.inr (.inl (by change c + s • v = c; simp [zero])))
  have orth_u : inner ℝ w u = 0 := by
    have eq (r : ℝ) : a - q s + r • u = p r - q s := by dsimp [p, u]; abel
    change inner ℝ (p t - q s) u = 0
    rw [← eq t]
    apply inner_eq_zero_of_min_affine_norm_sq _ _ t_int
    intro r hr
    change ‖a - q s + t • u‖ ^ 2 ≤ ‖a - q s + r • u‖ ^ 2
    rw [eq t, eq r]
    have cmp := (isMinOn_iff.mp minimum) (r, s) (show (r, s) ∈ I ×ˢ I from ⟨hr, hs⟩)
    dsimp only [measure, Prod.fst, Prod.snd] at cmp
    exact cmp
  have orth_v : inner ℝ w v = 0 := by
    have eq (r : ℝ) : c - p t + r • v = -(p t - q r) := by dsimp [q, v]; abel
    have h := inner_eq_zero_of_min_affine_norm_sq (c - p t) v s_int (by
      intro r hr
      change ‖c - p t + s • v‖ ^ 2 ≤ ‖c - p t + r • v‖ ^ 2
      rw [eq s, eq r, norm_neg, norm_neg]
      have cmp := (isMinOn_iff.mp minimum) (t, r) (show (t, r) ∈ I ×ˢ I from ⟨ht, hr⟩)
      dsimp only [measure, Prod.fst, Prod.snd] at cmp
      exact cmp)
    rw [eq, inner_neg_left, neg_eq_zero] at h
    exact h
  have dependent : ¬ LinearIndependent ℝ ![u, v] := by
    intro independent
    have zero : (innerSL ℝ w).toLinearMap = 0 := by
      apply LinearMap.ext_on_range (independent.span_eq_top_of_card_eq_finrank (by simp [Plane]))
      intro i
      fin_cases i
      · exact orth_u
      · exact orth_v
    have h := DFunLike.congr_fun zero w
    change inner ℝ w w = 0 at h
    rw [real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] at h
    exact w_ne h
  have proportional : ∃ r : ℝ, r • v = u := by
    by_contra! absent
    exact dependent (linearIndependent_fin2.mpr ⟨v_ne, absent⟩)
  obtain ⟨r, eq⟩ := proportional
  have r_ne : r ≠ 0 := by
    intro zero
    rw [zero, zero_smul] at eq
    exact u_ne eq.symm
  obtain ⟨t', s', ht', hs', on_edge, same⟩ := exists_slide_to_parameter_edge t_int s_int r r_ne
  have displacement : p t' - q s' = p t - q s := by
    change (a + t' • u) - (c + s' • v) = (a + t • u) - (c + s • v)
    rw [same, ← eq]
    module
  apply minimizer t' s' ht' hs' ?_ (by dsimp [measure]; rw [displacement])
  rcases on_edge with first | last | last
  · exact .inr (.inl (by rw [first, p_param, AffineMap.lineMap_apply_one]))
  · exact .inr (.inr (.inl (by rw [last, q_param, AffineMap.lineMap_apply_zero])))
  · exact .inr (.inr (.inr (by rw [last, q_param, AffineMap.lineMap_apply_one])))

end Unfoldings
