module

public import Unfoldings.Geometry.FiniteConvexTrace
public import Unfoldings.Geometry.PiecewiseAffineConvex

/-! Local supporting planes along a finite convex cover imply convexity on a segment. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Set

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite I]

/-- Along a segment, a finite closed convex cover supplies an affine partition.
At every interior transition, a local support comparison gives the ordered
one-sided slopes needed for convexity. -/
theorem convexOn_line_of_linear_cover (cell : I → Set E)
    (closed : ∀ i, IsClosed (cell i)) (convex : ∀ i, Convex ℝ (cell i))
    (f : E → ℝ) (piece : I → E →ₗ[ℝ] ℝ) (agree : ∀ i x, x ∈ cell i → f x = piece i x)
    (p q : E) (cover : ∀ x ∈ segment ℝ p q, ∃ i, x ∈ cell i)
    (support : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i j, AffineMap.lineMap p q t ∈ cell i →
      AffineMap.lineMap p q t ∈ cell j → ∀ z ∈ cell j, piece i z ≤ piece j z) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => f (AffineMap.lineMap p q t)) := by
  obtain ⟨n, hn, time, increasing, start, finish, part, contained⟩ :=
    exists_finite_closed_convex_segment_partition cell closed convex p q cover
  let T (k : ℕ) : ℝ := (time ⟨min k n, Nat.lt_succ_of_le (min_le_right k n)⟩ : ℝ)
  let P (k : ℕ) : I := part ⟨min k (n - 1), (min_le_right _ _).trans_lt (by omega)⟩
  have T_eq (k : Fin (n + 1)) : T k.val = (time k : ℝ) := by
    apply congrArg (fun i => (time i : ℝ))
    exact Fin.ext (min_eq_left (Nat.le_of_lt_succ k.isLt))
  have P_eq (k : Fin n) : P k.val = part k := by
    apply congrArg part
    exact Fin.ext (min_eq_left (by omega))
  have T_ord : Monotone T := fun i j hij => increasing.monotone (min_le_min_right n hij)
  have T_zero : T 0 = 0 := by
    change T (0 : Fin (n + 1)).val = 0
    rw [T_eq, start]
    rfl
  have T_last : T n = 1 := by
    change T (Fin.last n).val = 1
    rw [T_eq, finish]
    rfl
  have T_pos (k : ℕ) (hk : k < n) : T k < T (k + 1) := by
    have lo := T_eq (⟨k, hk⟩ : Fin n).castSucc
    have hi := T_eq (⟨k, hk⟩ : Fin n).succ
    change T k = _ at lo
    change T (k + 1) = _ at hi
    rw [lo, hi]
    exact increasing Fin.castSucc_lt_succ
  let A (k : ℕ) := piece (P k) p
  let S (k : ℕ) := piece (P k) (q - p)
  have on_cell (k : ℕ) (hk : k < n) {t : ℝ} (member : t ∈ Icc (T k) (T (k + 1))) :
      AffineMap.lineMap p q t ∈ cell (P k) := by
    let i : Fin n := ⟨k, hk⟩
    have lo := T_eq i.castSucc
    have hi := T_eq i.succ
    change T k = _ at lo
    change T (k + 1) = _ at hi
    rw [lo, hi] at member
    have tpos := (time i.castSucc).property.1.trans member.1
    have tsmall := member.2.trans (time i.succ).property.2
    rw [show P k = part i from P_eq i]
    exact contained i ⟨t, tpos, tsmall⟩ member
  have formula (k : ℕ) (t : ℝ) :
      piece (P k) (AffineMap.lineMap p q t) = A k + S k * t := by
    rw [AffineMap.lineMap_apply_module', map_add, map_smul, smul_eq_mul, add_comm, mul_comm t]
  have fit (k : ℕ) (hk : k < n) (t : ℝ) (member : t ∈ Icc (T k) (T (k + 1))) :
      f (AffineMap.lineMap p q t) = A k + S k * t :=
    (agree _ _ (on_cell k hk member)).trans (formula k t)
  have joined (k : ℕ) (hk : k + 1 < n) :
      A k + S k * T (k + 1) = A (k + 1) + S (k + 1) * T (k + 1) := by
    exact (fit k (by omega) _ ⟨(T_pos k (by omega)).le, le_rfl⟩).symm.trans
      (fit (k + 1) hk _ ⟨le_rfl, (T_pos (k + 1) hk).le⟩)
  have rising (k : ℕ) (hk : k + 1 < n) : S k ≤ S (k + 1) := by
    have mid := T_pos k (by omega)
    have last := T_pos (k + 1) hk
    have interior : T (k + 1) ∈ Ioo (0 : ℝ) 1 := by
      have start_le : 0 ≤ T k := T_zero ▸ T_ord (Nat.zero_le k)
      have finish_le : T (k + 2) ≤ 1 := T_last ▸ T_ord (by omega)
      exact ⟨start_le.trans_lt mid, last.trans_le finish_le⟩
    have shared₁ := on_cell k (by omega) ⟨mid.le, le_rfl⟩
    have shared₂ := on_cell (k + 1) hk ⟨le_rfl, last.le⟩
    have tail := on_cell (k + 1) hk ⟨last.le, le_rfl⟩
    have tail_support := support _ interior (P k) (P (k + 1)) shared₁ shared₂ _ tail
    rw [formula k, formula (k + 1)] at tail_support
    have product : (S k - S (k + 1)) * (T (k + 2) - T (k + 1)) ≤ 0 := by
      nlinarith only [tail_support, joined k hk]
    exact sub_nonpos.mp (nonpos_of_mul_nonpos_left product (sub_pos.mpr last))
  have all_t (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      ∃ k < n, r ∈ Icc (T k) (T (k + 1)) := by
    have exists_top : ∃ j : ℕ, r ≤ T j := ⟨n, T_last.symm ▸ hr.2⟩
    let j := Nat.find exists_top
    have below : r ≤ T j := Nat.find_spec exists_top
    have small : j ≤ n := Nat.find_min' exists_top (T_last.symm ▸ hr.2)
    by_cases zero : j = 0
    · rw [zero, T_zero] at below
      have equal : r = 0 := le_antisymm below hr.1
      exact ⟨0, hn, by rw [equal, ← T_zero]; exact ⟨le_rfl, (T_pos 0 hn).le⟩⟩
    · refine ⟨j - 1, by omega, ?_, ?_⟩
      · exact (lt_of_not_ge (Nat.find_min exists_top (show j - 1 < j by omega))).le
      · rwa [show j - 1 + 1 = j by omega]
  exact convexOn_of_monotone_affine_partition n T T_ord S A rising joined
    (convex_Icc 0 1) _ all_t fit

end Unfoldings
