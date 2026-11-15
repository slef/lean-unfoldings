module

public import Unfoldings.Geometry.AffineArrangement
public import Unfoldings.Geometry.EventualRayCell

/-! Both sides of a cut line have complete terminal cells, including rays on the line itself. -/

@[expose] public section

namespace Unfoldings.AffineArrangement

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite I]

/-- In a finite closed cover aligned to an affine level, cells on one specified
side cover that entire closed halfspace, including its boundary. -/
theorem mem_iUnion_cells_on_side (cells : I → Set E) (closed : ∀ i, IsClosed (cells i))
    (cover : (⋃ i, cells i) = Set.univ) (f : E →ᵃ[ℝ] ℝ) (signs : I → Bool)
    (aligned : ∀ i x, x ∈ cells i → 0 ≤ signed f (signs i) x)
    (side : Bool) (positive : ∃ q, 0 < signed f side q)
    {p : E} (weak : 0 ≤ signed f side p) :
    p ∈ ⋃ i : {i // signs i = side}, cells i.val := by
  classical
  let S := ⋃ i : {i // signs i = side}, cells i.val
  have closed_S : IsClosed S := isClosed_iUnion_of_finite (fun i => closed i.val)
  have strict_subset : {x | 0 < signed f side x} ⊆ S := by
    intro x hx
    have covered : x ∈ ⋃ i, cells i := cover.symm ▸ Set.mem_univ x
    obtain ⟨i, member⟩ := Set.mem_iUnion.mp covered
    have on_side : signs i = side := by
      have lower := aligned i x member
      cases side <;> cases value : signs i <;> simp_all [signed] <;> linarith
    exact Set.mem_iUnion.mpr ⟨⟨i, on_side⟩, member⟩
  obtain ⟨q, hq⟩ := positive
  have segment : openSegment ℝ q p ⊆ {x | 0 < signed f side x} := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := (openSegment_eq_image_lineMap ℝ q p).le hx
    change 0 < signed f side (AffineMap.lineMap q p t)
    rw [(signed f side).apply_lineMap, AffineMap.lineMap_apply_module]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr ht.2) hq) (mul_nonneg ht.1.le weak)
  exact closure_minimal (segment.trans strict_subset) closed_S
    (segment_subset_closure_openSegment (right_mem_segment ℝ q p))

/-- A nonzero affine level passing through a point has points strictly on each side. -/
theorem exists_signed_pos_of_zero (f : E →ᵃ[ℝ] ℝ) (proper : f ≠ 0)
    {p : E} (zero : f p = 0) (side : Bool) : ∃ q, 0 < signed f side q := by
  have nonzero : ∃ q, f q ≠ 0 := by
    by_contra absent
    apply proper
    ext q
    exact not_exists_not.mp absent q
  obtain ⟨q, hq⟩ := nonzero
  have reflected : f (AffineMap.lineMap q p (2 : ℝ)) = -f q := by
    rw [f.apply_lineMap, AffineMap.lineMap_apply_module, zero]
    ring
  cases side
  · by_cases positive : 0 < f q
    · exact ⟨AffineMap.lineMap q p (2 : ℝ), by
        change 0 < -f (AffineMap.lineMap q p (2 : ℝ))
        rw [reflected, neg_neg]
        exact positive⟩
    · exact ⟨q, by simpa [signed] using neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt positive) hq)⟩
  · by_cases positive : 0 < f q
    · exact ⟨q, by simpa [signed] using positive⟩
    · exact ⟨AffineMap.lineMap q p (2 : ℝ), by
        change 0 < f (AffineMap.lineMap q p (2 : ℝ))
        rw [reflected]
        exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt positive) hq)⟩

/-- A ray on an aligned cut line eventually lies in an actual cell on either chosen side.
The side is supplied, but the cell and the finite starting threshold are constructed. -/
theorem exists_eventual_ray_cell_on_side (cells : I → Set E)
    (closed : ∀ i, IsClosed (cells i)) (convex : ∀ i, Convex ℝ (cells i))
    (cover : (⋃ i, cells i) = Set.univ) (f : E →ᵃ[ℝ] ℝ) (proper : f ≠ 0)
    (signs : I → Bool) (aligned : ∀ i x, x ∈ cells i → 0 ≤ signed f (signs i) x)
    (p d : E) (on_line : ∀ t : ℝ, f (p + t • d) = 0) (side : Bool) :
    ∃ i : I, signs i = side ∧ ∃ T : ℝ, 0 ≤ T ∧
      ∀ t : ℝ, T ≤ t → p + t • d ∈ cells i := by
  have zero : f p = 0 := by simpa using on_line 0
  obtain ⟨i, T, positive, tail⟩ := Unfoldings.exists_eventual_ray_cell
    (fun i : {i // signs i = side} => cells i.val) (fun i => convex i.val) p d
    (fun t _ => mem_iUnion_cells_on_side cells closed cover f signs aligned side
      (exists_signed_pos_of_zero f proper zero side)
      (by simp only [signed_apply, on_line, neg_zero, ite_self, le_refl]))
  exact ⟨i.val, i.property, T, positive, tail⟩

end Unfoldings.AffineArrangement
