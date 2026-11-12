module

public import Unfoldings.Cap.SharedSectorBankCoordinates

/-! Shared physical bank points have an exact order despite their different height scales. -/

@[expose] public section

namespace Unfoldings

theorem shared_sector_bank_point_order {t : ℝ} (positive : 0 < t) (small : t < 1)
    {i j : FiveSector} (shared : fiveSectorFirst t i = fiveSectorLast t j)
    {h k : ℝ} (first_positive : 0 < h) (last_positive : 0 < k) :
    (∃ a ∈ Set.Ioc 0 k,
      (fiveSectorFrame t positive small i).place.symm
          ((fiveSectorFrame t positive small i).enclosingStrip.upper.point h) =
        (fiveSectorFrame t positive small j).place.symm
          ((fiveSectorFrame t positive small j).enclosingStrip.lower.point a)) ∨
    (∃ b ∈ Set.Ioc 0 h,
      (fiveSectorFrame t positive small j).place.symm
          ((fiveSectorFrame t positive small j).enclosingStrip.lower.point k) =
        (fiveSectorFrame t positive small i).place.symm
          ((fiveSectorFrame t positive small i).enclosingStrip.upper.point b)) := by
  let first := fiveSectorFrame t positive small i
  let last := fiveSectorFrame t positive small j
  let z := last.place (first.place.symm (first.enclosingStrip.upper.point h))
  let a := z.re + z.im
  have converted :=
    fiveSector_shared_upper_to_lower_coordinates positive small shared first_positive
  have positive_a : 0 < a := converted.1
  have at_a : z = last.enclosingStrip.lower.point a := converted.2
  have contact : first.place.symm (first.enclosingStrip.upper.point h) =
      last.place.symm (last.enclosingStrip.lower.point a) := by
    have inverse := congrArg last.place.symm at_a
    rw [last.place.symm_apply_apply] at inverse
    exact inverse
  rcases le_total a k with before | after
  · exact Or.inl ⟨a, ⟨positive_a, before⟩, contact⟩
  · let r := k / a
    have rpositive : 0 < r := div_pos last_positive positive_a
    have rbound : r ≤ 1 := (div_le_one positive_a).mpr after
    have product : r * a = k := div_mul_cancel₀ _ positive_a.ne'
    have last_homogeneous : last.enclosingStrip.lower.point k =
        r • last.enclosingStrip.lower.point a :=
      (congrArg last.enclosingStrip.lower.point product.symm).trans
        (last.enclosingStrip_lower_point_smul rpositive.le positive_a.le)
    refine Or.inr ⟨r * h, ⟨mul_pos rpositive first_positive, ?_⟩, ?_⟩
    · nlinarith
    · rw [last_homogeneous, map_smul, ← contact,
        first.enclosingStrip_upper_point_smul rpositive.le first_positive.le, map_smul]

end Unfoldings
