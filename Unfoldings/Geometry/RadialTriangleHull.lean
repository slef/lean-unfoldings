module

public import Unfoldings.Geometry.RadialLinearCoverConvex
public import Mathlib.Analysis.Convex.Combination

/-! The sublevel body of a radial triangle gauge is the hull of the sites. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Set
open scoped BigOperators

/-- The radial cone of a chord triangle, with its apex at the origin. -/
def radialTriangleCone (v : Fin 3 → Space) : Set Space :=
  {x | ∃ w : Fin 3 → ℝ, (∀ k, 0 ≤ w k) ∧ x = ∑ k, w k • v k}

theorem corner_mem_radialTriangleCone (v : Fin 3 → Space) (i : Fin 3) :
    v i ∈ radialTriangleCone v := by
  classical
  let w : Fin 3 → ℝ := Pi.single i 1
  refine ⟨w, fun j => ?_, ?_⟩
  · simp [w, Pi.single_apply, apply_ite]
  · simp [w, Pi.single_apply]

/-- The gauge sends every ray section to the sum of its cone coordinates.
Its unit sublevel set is the convex hull of the corners and its apex. -/
theorem convexHull_eq_sublevel_of_radial_triangles {I : Type*}
    (v : I → Fin 3 → Space) (cover : ∀ x, ∃ i, x ∈ radialTriangleCone (v i))
    (f : Space → ℝ) (convex : ConvexOn ℝ Set.univ f)
    (plane : I → Space →ₗ[ℝ] ℝ) (unit : ∀ i j, plane i (v i j) = 1)
    (agree : ∀ i x, x ∈ radialTriangleCone (v i) → f x = plane i x) :
    convexHull ℝ (insert 0 (range (fun ij : I × Fin 3 => v ij.1 ij.2))) =
      {x | f x ≤ 1} := by
  let sites := insert 0 (range (fun ij : I × Fin 3 => v ij.1 ij.2))
  let body := convexHull ℝ sites
  have zero : f 0 = 0 := by
    obtain ⟨i, present⟩ := cover 0
    exact (agree i 0 present).trans (map_zero (plane i))
  apply le_antisymm
  · apply convexHull_min
    · rintro x (rfl | ⟨⟨i, j⟩, rfl⟩)
      · change f 0 ≤ 1
        rw [zero]
        norm_num
      · change f (v i j) ≤ 1
        exact (agree i _ (corner_mem_radialTriangleCone (v i) j)).trans (unit i j) |>.le
    · simpa only [mem_univ, true_and] using convex.convex_le 1
  · rintro x (small : f x ≤ 1)
    obtain ⟨i, cone⟩ := cover x
    have at_x := agree i x cone
    obtain ⟨w, nonneg, eq⟩ := cone
    have sum_eq : f x = ∑ j, w j := by
      rw [at_x, eq, map_sum]
      simp only [map_smul, smul_eq_mul, unit, mul_one]
    have bound : (∑ j, w j) ≤ 1 := sum_eq ▸ small
    let coeff : Fin 4 → ℝ := Fin.cons (1 - ∑ j, w j) w
    let point : Fin 4 → Space := Fin.cons 0 (v i)
    have positive (j : Fin 4) : 0 ≤ coeff j := by
      refine Fin.cases ?_ (fun k => ?_) j
      · exact sub_nonneg.mpr bound
      · exact nonneg k
    have total : (∑ j : Fin 4, coeff j) = 1 := by
      rw [Fin.sum_univ_succ]
      simp [coeff]
    have member (j : Fin 4) : point j ∈ body := by
      apply subset_convexHull ℝ sites
      refine Fin.cases ?_ (fun k => ?_) j
      · exact Or.inl rfl
      · exact Or.inr ⟨(i, k), rfl⟩
    have inside := (convex_convexHull ℝ sites).sum_mem (t := Finset.univ)
      (fun j _ => positive j) total (fun j _ => member j)
    rw [Fin.sum_univ_succ] at inside
    simpa only [coeff, point, Fin.cons_zero, Fin.cons_succ, smul_zero, zero_add, ← eq] using inside

end Unfoldings
