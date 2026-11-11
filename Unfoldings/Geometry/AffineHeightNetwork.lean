module

public import Unfoldings.Geometry.HeightSegmentNetwork

/-! Transport forward-deterministic affine segments into a height network. -/

@[expose] public section

noncomputable section

namespace Unfoldings.HeightSegmentNetwork

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]

def ofAffineSegments (A : E ≃ᵃ[ℝ] ℂ) (first last : ι → E)
    (ascending : ∀ i, complexDiagonalHeight (A (first i)) < complexDiagonalHeight (A (last i)))
    (unique : ∀ i j (x : E), x ∈ segment ℝ (first i) (last i) → x ≠ last i →
      x ∈ segment ℝ (first j) (last j) → x ≠ last j → i = j) : HeightSegmentNetwork ι where
  first i := A (first i)
  last i := A (last i)
  ascending := ascending
  forward_unique := by
    intro i j x first_mem first_not_end last_mem last_not_end
    have pull {p q : E} (member : x ∈ segment ℝ (A p) (A q)) : A.symm x ∈ segment ℝ p q := by
      have image : A '' segment ℝ p q = segment ℝ (A p) (A q) :=
        image_segment ℝ A.toAffineMap p q
      obtain ⟨y, inside, equal⟩ := image.symm.subset member
      have inverse : y = A.symm x := (A.symm_apply_apply y).symm.trans (congrArg A.symm equal)
      exact inverse ▸ inside
    apply unique i j (A.symm x) (pull first_mem) _ (pull last_mem)
    · intro equal
      exact last_not_end (by simpa only [A.apply_symm_apply] using congrArg A equal)
    · intro equal
      exact first_not_end (by simpa only [A.apply_symm_apply] using congrArg A equal)

end Unfoldings.HeightSegmentNetwork
