module

public import Unfoldings.Geometry.ThreeSectorFrames

/-! Add two acute forward sectors to cover every direction on the extended roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings

abbrev FiveSector := Fin 3 ⊕ Bool

def forwardSectorRay : Plane := WithLp.toLp 2 ![1, 0]

def fiveSectorFirst (t : ℝ) : FiveSector → Plane :=
  Sum.elim (fun i => threeSectorRay t i.castSucc)
    (fun upper => if upper then forwardSectorRay else threeSectorRay t 3)

def fiveSectorLast (t : ℝ) : FiveSector → Plane :=
  Sum.elim (fun i => threeSectorRay t i.succ)
    (fun upper => if upper then threeSectorRay t 0 else forwardSectorRay)

def closedFiveSector (t : ℝ) (i : FiveSector) : Set Plane :=
  {x | InDirectionWedge (fiveSectorFirst t i) (fiveSectorLast t i) x}

theorem fiveSector_banks_inner_pos {t : ℝ} (positive : 0 < t) (small : t < 1) (i : FiveSector) :
    0 < inner ℝ (fiveSectorFirst t i) (fiveSectorLast t i) := by
  cases i with
  | inl i => exact threeSector_banks_inner_pos positive small i
  | inr upper =>
    cases upper <;>
      norm_num [fiveSectorFirst, fiveSectorLast, forwardSectorRay, threeSectorRay,
        PiLp.inner_apply, Fin.sum_univ_two] <;> linarith

theorem fiveSector_banks_orient_pos {t : ℝ} (positive : 0 < t) (small : t < 1) (i : FiveSector) :
    0 < orient 0 (fiveSectorFirst t i) (fiveSectorLast t i) := by
  cases i with
  | inl i => exact threeSector_banks_orient_pos positive small i
  | inr upper =>
    cases upper <;>
      norm_num [fiveSectorFirst, fiveSectorLast, forwardSectorRay, threeSectorRay, orient] <;>
        linarith

theorem fiveSector_width_lt_pi_div_two {t : ℝ} (positive : 0 < t) (small : t < 1)
    (i : FiveSector) :
    InnerProductGeometry.angle (fiveSectorFirst t i) (fiveSectorLast t i) < Real.pi / 2 := by
  apply lt_of_not_ge
  intro wide
  exact (not_lt_of_ge (InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mpr wide))
    (fiveSector_banks_inner_pos positive small i)

/-- Auxiliary roof vertices may lie in the old forward gap. These five acute sectors cover them
as well as the original three backward sectors, with no empty-gap assumption. -/
theorem exists_mem_closedFiveSector {t : ℝ} (positive : 0 < t) (small : t < 1) (p : Plane) :
    ∃ i : FiveSector, p ∈ closedFiveSector t i := by
  by_cases backward : p 0 ≤ 0
  · obtain ⟨i, inside⟩ := mem_closedThreeSector_of_backward positive.le small backward
    exact ⟨Sum.inl i, inDirectionWedge_of_closedThreeSector positive.le small i inside⟩
  have rightward : 0 < p 0 := lt_of_not_ge backward
  have denominator : 0 < 1 + t := by linarith
  by_cases upper : 0 ≤ p 1
  · by_cases old : 0 ≤ (1 - t) * p 1 - (1 + t) * p 0
    · refine ⟨Sum.inl 0, inDirectionWedge_of_closedThreeSector positive.le small 0 ?_⟩
      change 0 ≤ (1 - t) * p 0 + p 1 ∧ _
      exact ⟨add_nonneg (mul_nonneg (by linarith) rightward.le) upper, old⟩
    · let a := p 0 - (1 - t) * p 1 / (1 + t)
      let b := p 1 / (1 + t)
      have anonnegative : 0 ≤ a := sub_nonneg.mpr
        ((div_le_iff₀ denominator).mpr (by nlinarith [lt_of_not_ge old]))
      refine ⟨Sum.inr true, a, b, anonnegative, div_nonneg upper denominator.le, ?_⟩
      ext j
      fin_cases j <;> norm_num [fiveSectorFirst, fiveSectorLast, forwardSectorRay,
        threeSectorRay, a, b] <;> field_simp [denominator.ne']
      ring
  · have lower : p 1 ≤ 0 := (lt_of_not_ge upper).le
    by_cases old : 0 ≤ -(1 + t) * p 0 - (1 - t) * p 1
    · refine ⟨Sum.inl 2, inDirectionWedge_of_closedThreeSector positive.le small 2 ?_⟩
      change 0 ≤ -(1 + t) * p 0 - (1 - t) * p 1 ∧ 0 ≤ (1 - t) * p 0 - p 1
      exact ⟨old, sub_nonneg.mpr (lower.trans (mul_nonneg (by linarith) rightward.le))⟩
    · let a := -p 1 / (1 + t)
      let b := p 0 - (1 - t) * (-p 1) / (1 + t)
      have bnonnegative : 0 ≤ b := sub_nonneg.mpr
        ((div_le_iff₀ denominator).mpr (by nlinarith [lt_of_not_ge old]))
      refine ⟨Sum.inr false, a, b, div_nonneg (neg_nonneg.mpr lower) denominator.le,
        bnonnegative, ?_⟩
      ext j
      fin_cases j <;> norm_num [fiveSectorFirst, fiveSectorLast, forwardSectorRay,
        threeSectorRay, a, b] <;> field_simp [denominator.ne'] <;> ring

end Unfoldings
