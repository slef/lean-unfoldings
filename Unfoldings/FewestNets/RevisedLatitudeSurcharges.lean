module

public import Unfoldings.FewestNets.RevisedLatitudeAnnularCorners
public import Unfoldings.FewestNets.RevisedLatitudeCountBounds

/-! Only the two polar strips contribute extra apex charges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

include positive small

private theorem one_lt_stripCount : 1 < stripCount a := by
  have lower := Nat.le_ceil ((π - 2 * AcuteLatitudeGrid.polarRadius a) / radius a)
  have fraction : 1 < (π - 2 * AcuteLatitudeGrid.polarRadius a) / radius a :=
    (lt_div_iff₀ (radius_pos positive)).mpr (by
      linarith only [radius_lt small, AcuteLatitudeGrid.polarRadius_lt small, pi_gt_d2])
  exact_mod_cast fraction.trans_le lower

private theorem nearPolar_rowSize_lt :
    (rowSize a 1 : ℝ) < 14.5 / a ∧
      (rowSize a (stripCount a - 1) : ℝ) < 14.5 / a := by
  let k := stripCount a
  let ρ := AcuteLatitudeGrid.polarRadius a
  let r := radius a
  let d := rowStep a
  have two : 1 < k := one_lt_stripCount positive small
  have Cp : 0 < ρ + d := add_pos (AcuteLatitudeGrid.polarRadius_pos positive) (rowStep_pos positive small)
  have first : colatitude a 1 = ρ + d := by simp [colatitude, ρ, d]
  have last : colatitude a (k - 1) = π - (ρ + d) := by
    have last_succ : k - 1 + 1 = k := by omega
    have identity := colatitude_succ (a := a) (k - 1)
    rw [last_succ, colatitude_last positive small] at identity
    change π - ρ = colatitude a (k - 1) + d at identity
    linarith only [identity]
  have radius_ratio : ρ = r / 8.64 := by
    have h := radius_eq_polarRadius a
    change r = 8.64 * ρ at h
    ring_nf at h ⊢
    linarith only [h]
  have row {j : ℕ} (lower : 0 < j) (upper : j < k)
      (he : sin (colatitude a j) = sin (ρ + d)) :
      (rowSize a j : ℝ) < 14.5 / a := by
    let q := 2 * π * sin (ρ + d) / spacing a
    have sine_pos : 0 ≤ sin (ρ + d) := by
      rw [← he]
      exact (sin_pos_of_mem_Ioo (colatitude_mem positive small upper.le)).le
    have qp : 0 ≤ q := div_nonneg (mul_nonneg (by positivity) sine_pos) (spacing_pos positive).le
    have row : rowSize a j = ⌈q⌉₊ := by
      unfold rowSize
      rw [ite_eq_right (not_or.mpr ⟨lower.ne', upper.ne⟩), he]
    rw [row]
    apply (lt_div_iff₀ positive).mpr
    have ceil := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one qp) positive
    have sample : q * a ≤ 2 * π * (1 + 1 / 8.64) / 0.51 := by
      have sine_le := sin_le Cp.le
      have rstep : d ≤ r := (rowStep_bounds positive small).2
      have upper : sin (ρ + d) ≤ (1 + 1 / 8.64) * r := sine_le.trans (by
        rw [radius_ratio]
        ring_nf
        linarith only [rstep])
      calc
        q * a ≤ (2 * π * ((1 + 1 / 8.64) * r) / spacing a) * a :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left upper (by positivity)) (spacing_pos positive).le) positive.le
        _ = _ := by
          rw [spacing]
          change (2 * π * ((1 + 1 / 8.64) * r) / (0.51 * a * r)) * a = _
          have rp : 0 < r := radius_pos positive
          field_simp [positive.ne', rp.ne'] <;> ring
    ring_nf at ceil sample ⊢
    linarith only [ceil, sample, small, pi_lt_d6]
  exact ⟨row (by omega) two (congrArg sin first),
    row (by omega) (by omega) (by rw [last, sin_pi_sub])⟩

theorem annularApexCoefficient_sum :
    (∑ i : AnnularTriangle a, (annularApexCoefficient i - 1.225)) =
      1.545 * ((rowSize a 0 : ℝ) + rowSize a (stripCount a)) +
        0.03 * ((rowSize a 1 : ℝ) + rowSize a (stripCount a - 1)) := by
  let J := stripCount a
  have strip := one_lt_stripCount positive small
  let first : Fin J := ⟨0, by omega⟩
  let last : Fin J := ⟨J - 1, by omega⟩
  let A (j : Fin J) : ℝ := 1.545 * rowSize a j.val + 0.03 * rowSize a (j.val + 1)
  let B (j : Fin J) : ℝ := 0.03 * rowSize a j.val + 1.545 * rowSize a (j.val + 1)
  have local_sum (j : Fin J) :
      (∑ k : Fin (rowSize a j.val + rowSize a (j.val + 1)),
        (annularApexCoefficient ⟨j, k⟩ - 1.225)) =
          (if j = first then A j else 0) + (if j = last then B j else 0) := by
    let e := LatitudeRings.sweepOrder (rowSize a j.val) (rowSize a (j.val + 1))
    let f : Fin (rowSize a j.val) ⊕ Fin (rowSize a (j.val + 1)) → ℝ :=
      Sum.elim (fun _ => apexCountCoefficient (isPolarStrip a j.val) (isPolarRow a j.val) - 1.225)
        (fun _ => apexCountCoefficient (isPolarStrip a j.val) (isPolarRow a (j.val + 1)) - 1.225)
    have pointwise (k : Fin (rowSize a j.val + rowSize a (j.val + 1))) :
        (annularApexCoefficient ⟨j, k⟩ - 1.225) = f (e k) := by
      unfold annularApexCoefficient baseRow e f
      dsimp only
      cases h : LatitudeRings.sweepOrder (rowSize a j.val) (rowSize a (j.val + 1)) k <;>
        simp only [h, Sum.elim_inl, Sum.elim_inr]
    simp_rw [pointwise]
    rw [Equiv.sum_comp e f, Fintype.sum_sum_type]
    simp only [f, Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have jp : j.val < J := j.isLt
    have nn : j.val + 1 ≠ 0 := by omega
    have not_self : j.val ≠ J := jp.ne
    have at_first : j = first ↔ j.val = 0 := ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
    have at_last : j = last ↔ j.val + 1 = J := by
      constructor
      · intro eq
        have q : j.val = J - 1 := congrArg Fin.val eq
        omega
      · intro eq
        apply Fin.ext
        change j.val = J - 1
        omega
    by_cases h₀ : j.val = 0 <;> by_cases h₁ : j.val + 1 = J
    · omega
    · have eq : j = first := at_first.mpr h₀
      have ne : j ≠ last := fun h => h₁ (at_last.mp h)
      have lower : isPolarRow a j.val = true := decide_eq_true (Or.inl h₀)
      have upper : isPolarRow a (j.val + 1) = false :=
        decide_eq_false_iff_not.mpr (not_or.mpr ⟨nn, h₁⟩)
      rw [ite_eq_left eq, ite_eq_right ne]
      norm_num [isPolarStrip, lower, upper, apexCountCoefficient, A]
      ring
    · have eq : j = last := at_last.mpr h₁
      have ne : j ≠ first := fun h => h₀ (at_first.mp h)
      have lower : isPolarRow a j.val = false :=
        decide_eq_false_iff_not.mpr (not_or.mpr ⟨h₀, not_self⟩)
      have upper : isPolarRow a (j.val + 1) = true := decide_eq_true (Or.inr h₁)
      rw [ite_eq_right ne, ite_eq_left eq]
      norm_num [isPolarStrip, lower, upper, apexCountCoefficient, B]
      ring
    · have lo : j ≠ first := fun h => h₀ (at_first.mp h)
      have hi : j ≠ last := fun h => h₁ (at_last.mp h)
      have lower : isPolarRow a j.val = false :=
        decide_eq_false_iff_not.mpr (not_or.mpr ⟨h₀, not_self⟩)
      have upper : isPolarRow a (j.val + 1) = false :=
        decide_eq_false_iff_not.mpr (not_or.mpr ⟨nn, h₁⟩)
      rw [ite_eq_right lo, ite_eq_right hi]
      norm_num [isPolarStrip, lower, upper, apexCountCoefficient]
  rw [Fintype.sum_sigma]
  simp_rw [local_sum]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, A, B]
  have last_succ : J - 1 + 1 = J := by omega
  change 1.545 * (rowSize a 0 : ℝ) + 0.03 * (rowSize a (0 + 1) : ℝ) +
    (0.03 * (rowSize a (J - 1) : ℝ) + 1.545 * (rowSize a (J - 1 + 1) : ℝ)) = _
  rw [last_succ]
  ring

theorem annularApexCoefficient_excess_lt :
    (∑ i : AnnularTriangle a, (annularApexCoefficient i - 1.225)) <
      (1.545 * 6.3 + 0.03 * 29) / a := by
  rw [annularApexCoefficient_sum positive small, rowSize_at_poles.1, rowSize_at_poles.2]
  obtain ⟨north, south⟩ := nearPolar_rowSize_lt positive small
  have poles := (polarSize_bounds positive small).2.1
  rw [add_div, mul_div_assoc, mul_div_assoc]
  ring_nf at poles north south ⊢
  linarith only [north, south, poles]

end Unfoldings.FewestNets.RevisedLatitudeGrid
