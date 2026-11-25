module

public import Unfoldings.Geometry.SphericalConvex
public import Mathlib.Data.Finset.Max

/-! A central hit fixes the selector membership on each side of its great circle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

/-- The first support plane crossed along a normalized chord is itself a
boundary point. This gives the cell's membership from the unique support
side it intersects and a point strict on every other support. -/
theorem mem_central_selector_iff_positive {I : Type*} [Finite I] (f : I → Space →ₗ[ℝ] ℝ)
    {N : Set Space} (convex : SphericalConvex N) (i : I) {x q : Space}
    (x_in : x ∈ N) (q_in : q ∈ N) (x_zero : f i x = 0)
    (x_strict : ∀ j ≠ i, 0 < f j x)
    (one_side : ∀ z ∈ N, (∀ j, 0 ≤ f j z) → ∀ j, f j z = 0 → j = i)
    (generic : f i q ≠ 0) :
    (∀ j, 0 ≤ f j q) ↔ 0 < f i q := by
  classical
  let : Fintype I := Fintype.ofFinite I
  constructor
  · exact fun all => (all i).lt_of_ne generic.symm
  · intro positive
    by_contra! outside
    let bad : Finset I := Finset.univ.filter fun j => f j q < 0
    let time (j : I) := f j x / (f j x - f j q)
    have present : bad.Nonempty := by
      obtain ⟨j, negative⟩ := outside
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, negative⟩⟩
    have bad_negative (j : I) (mem : j ∈ bad) : f j q < 0 := (Finset.mem_filter.mp mem).2
    have bad_other (j : I) (mem : j ∈ bad) : j ≠ i := fun equal =>
      (bad_negative j mem).not_ge (equal ▸ positive.le)
    have bad_start (j : I) (mem : j ∈ bad) : 0 < f j x := x_strict j (bad_other j mem)
    obtain ⟨k, marked, least⟩ := Finset.exists_min_image bad time present
    let t := time k
    have t_pos : 0 < t :=
      div_pos (bad_start k marked) (sub_pos.mpr ((bad_negative k marked).trans (bad_start k marked)))
    have t_small : t < 1 :=
      (div_lt_one (sub_pos.mpr ((bad_negative k marked).trans (bad_start k marked)))).mpr
        (by linarith only [bad_negative k marked])
    let z := (1 - t) • x + t • q
    have evaluation (j : I) : f j z = (1 - t) * f j x + t * f j q := by
      simp only [z, map_add, map_smul, smul_eq_mul]
    have crossed : f k z = 0 := by
      rw [evaluation]
      have exact_time := div_mul_cancel₀ (f k x)
        (sub_pos.mpr ((bad_negative k marked).trans (bad_start k marked))).ne'
      change t * (f k x - f k q) = f k x at exact_time
      linarith only [exact_time]
    have h_pos : 0 < f i z := by rw [evaluation, x_zero, mul_zero, zero_add]; exact mul_pos t_pos positive
    have supported (j : I) : 0 ≤ f j z := by
      by_cases sign : f j q < 0
      · have member : j ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, sign⟩
        have below := (le_div_iff₀ (sub_pos.mpr (sign.trans (bad_start j member)))).mp
          (least j member)
        rw [evaluation]
        linarith only [below]
      · rw [evaluation]
        have starts : 0 ≤ f j x := by
          by_cases equal : j = i
          · exact equal ▸ x_zero.ge
          · exact (x_strict j equal).le
        exact add_nonneg (mul_nonneg (sub_nonneg.mpr t_small.le) starts)
          (mul_nonneg t_pos.le (le_of_not_gt sign))
    have genuine : z ≠ 0 := fun zero => h_pos.ne' (by rw [zero, map_zero])
    let point := NormedSpace.normalize z
    have point_in : point ∈ N :=
      convex.2 x x_in q q_in (1 - t) t (sub_nonneg.mpr t_small.le) t_pos.le genuine
    have point_supported (j : I) : 0 ≤ f j point := by
      simp only [point, NormedSpace.normalize, map_smul, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (supported j)
    have hits : f k point = 0 := by
      simp only [point, NormedSpace.normalize, map_smul, smul_eq_mul, crossed, mul_zero]
    exact bad_other k marked (one_side point point_in point_supported k hits)

end Unfoldings.FewestNets
