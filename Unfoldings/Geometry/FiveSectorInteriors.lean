module

public import Unfoldings.Geometry.FiveSectors
public import Unfoldings.Geometry.CyclicRays

/-! Exact algebraic tests distinguish sector interiors from their shared boundary rays. -/

@[expose] public section

namespace Unfoldings

def fiveSectorCoordinates (t : ℝ) : FiveSector → Plane →ₗ[ℝ] Plane
  | Sum.inl i => threeSectorCoordinates t i
  | Sum.inr upper =>
    { toFun x := if upper then WithLp.toLp 2 ![(1 + t) * x 0 - (1 - t) * x 1, x 1]
        else WithLp.toLp 2 ![-x 1, (1 + t) * x 0 + (1 - t) * x 1]
      map_add' x y := by cases upper <;> ext j <;> fin_cases j <;> simp <;> ring
      map_smul' r x := by cases upper <;> ext j <;> fin_cases j <;> simp <;> ring }

def fiveSectorDet (t : ℝ) : FiveSector → ℝ :=
  Sum.elim (threeSectorDet t) (fun _ => 1 + t)

def strictFiveSector (t : ℝ) (i : FiveSector) : Set Plane :=
  {x | 0 < fiveSectorCoordinates t i x 0 ∧ 0 < fiveSectorCoordinates t i x 1}

theorem fiveSectorDet_pos {t : ℝ} (positive : 0 < t) (small : t < 1) (i : FiveSector) :
    0 < fiveSectorDet t i := by
  cases i with
  | inl i => exact threeSectorDet_pos positive.le small i
  | inr upper => change 0 < 1 + t; linarith

theorem fiveSectorCoordinates_first (t : ℝ) (i : FiveSector) :
    fiveSectorCoordinates t i (fiveSectorFirst t i) = WithLp.toLp 2 ![fiveSectorDet t i, 0] := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [fiveSectorCoordinates, fiveSectorFirst, fiveSectorDet, threeSectorCoordinates,
      threeSectorRay, threeSectorDet, forwardSectorRay] <;> ring

theorem fiveSectorCoordinates_last (t : ℝ) (i : FiveSector) :
    fiveSectorCoordinates t i (fiveSectorLast t i) = WithLp.toLp 2 ![0, fiveSectorDet t i] := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [fiveSectorCoordinates, fiveSectorLast, fiveSectorDet, threeSectorCoordinates,
      threeSectorRay, threeSectorDet, forwardSectorRay] <;> ring

theorem closedFiveSector_coordinates {t : ℝ} (positive : 0 < t) (small : t < 1)
    (i : FiveSector) {x : Plane} (inside : x ∈ closedFiveSector t i) :
    0 ≤ fiveSectorCoordinates t i x 0 ∧ 0 ≤ fiveSectorCoordinates t i x 1 := by
  obtain ⟨a, b, ha, hb, equal⟩ := inside
  rw [equal, map_add, map_smul, map_smul, fiveSectorCoordinates_first, fiveSectorCoordinates_last]
  change 0 ≤ a * fiveSectorDet t i + b * 0 ∧ 0 ≤ a * 0 + b * fiveSectorDet t i
  simpa only [mul_zero, zero_add, add_zero] using
    And.intro (mul_nonneg ha (fiveSectorDet_pos positive small i).le)
      (mul_nonneg hb (fiveSectorDet_pos positive small i).le)

theorem strictRayCone_subset_strictFiveSector {t : ℝ} (positive : 0 < t) (small : t < 1)
    (i : FiveSector) : strictRayCone (fiveSectorFirst t i) (fiveSectorLast t i) ⊆
      strictFiveSector t i := by
  rintro x ⟨a, ha, b, hb, equal⟩
  change 0 < fiveSectorCoordinates t i x 0 ∧ 0 < fiveSectorCoordinates t i x 1
  rw [equal, map_add, map_smul, map_smul, fiveSectorCoordinates_first, fiveSectorCoordinates_last]
  change 0 < a * fiveSectorDet t i + b * 0 ∧ 0 < a * 0 + b * fiveSectorDet t i
  simpa only [mul_zero, zero_add, add_zero] using
    And.intro (mul_pos ha (fiveSectorDet_pos positive small i))
      (mul_pos hb (fiveSectorDet_pos positive small i))

theorem strictFiveSector_disjoint_closed {t : ℝ} (positive : 0 < t) (small : t < 1) :
    Pairwise (fun i j : FiveSector => Disjoint (strictFiveSector t i) (closedFiveSector t j)) := by
  intro i j different
  apply Set.disjoint_left.mpr
  intro x first last
  have closed := closedFiveSector_coordinates positive small j last
  change 0 < fiveSectorCoordinates t i x 0 ∧ 0 < fiveSectorCoordinates t i x 1 at first
  fin_cases i <;> fin_cases j <;>
    norm_num [fiveSectorCoordinates, threeSectorCoordinates] at first closed different
  all_goals
    by_cases horizontal : 0 ≤ x 0
    · nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - t) horizontal]
    · have product : (1 + t) * x 0 < 0 :=
        mul_neg_of_pos_of_neg (by linarith) (lt_of_not_ge horizontal)
      by_cases vertical : 0 ≤ x 1
      · nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - t) vertical]
      · nlinarith [mul_neg_of_pos_of_neg (by linarith : 0 < 1 - t)
          (lt_of_not_ge vertical)]

end Unfoldings
