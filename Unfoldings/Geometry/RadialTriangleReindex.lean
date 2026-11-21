module

public import Unfoldings.Geometry.RadialTriangleGauge

/-! Radial cones and gauges depend only on their corner positions. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Set
open scoped BigOperators

theorem sum_mem_radialTriangleCone {v w : Fin 3 → Space}
    (independent : LinearIndependent ℝ w) (c : Fin 3 → ℝ) (nonnegative : ∀ i, 0 ≤ c i)
    (sub : ∀ i, 0 < c i → v i ∈ Set.range w) :
    (∑ i, c i • v i) ∈ radialTriangleCone w := by
  apply (mem_radialTriangleCone_iff_basis independent).mpr
  intro j
  rw [map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_nonneg
  intro i _
  by_cases positive : 0 < c i
  · obtain ⟨k, hk⟩ := sub i positive
    rw [← hk]
    exact mul_nonneg (nonnegative i)
      ((mem_radialTriangleCone_iff_basis independent).mp (corner_mem_radialTriangleCone w k) j)
  · rw [le_antisymm (le_of_not_gt positive) (nonnegative i), zero_mul]

theorem radialTriangleCone_mono_range {v w : Fin 3 → Space}
    (independent : LinearIndependent ℝ w) (sub : Set.range v ⊆ Set.range w) :
    radialTriangleCone v ⊆ radialTriangleCone w := by
  rintro x ⟨c, nonnegative, rfl⟩
  exact sum_mem_radialTriangleCone independent c nonnegative (fun i _ => sub (Set.mem_range_self i))

theorem radialTriangleCone_eq_of_range_eq {v w : Fin 3 → Space}
    (left : LinearIndependent ℝ v) (right : LinearIndependent ℝ w)
    (same : Set.range v = Set.range w) :
    radialTriangleCone v = radialTriangleCone w :=
  (radialTriangleCone_mono_range right same.le).antisymm
    (radialTriangleCone_mono_range left same.ge)

theorem radialTriangleGauge_eq_of_range_eq {v w : Fin 3 → Space}
    (left : LinearIndependent ℝ v) (right : LinearIndependent ℝ w)
    (same : Set.range v = Set.range w) :
    radialTriangleGauge left = radialTriangleGauge right := by
  apply radialTriangleGauge_unique
  intro i
  obtain ⟨j, hj⟩ := same.le (Set.mem_range_self i)
  rw [← hj, radialTriangleGauge_corner]

theorem exists_fin_three_rest (i j : Fin 3) (h : i ≠ j) :
    ∃ k : Fin 3, i ≠ k ∧ j ≠ k ∧ ∀ l : Fin 3, l = i ∨ l = j ∨ l = k := by
  have table : ∀ i j : Fin 3, i ≠ j →
      ∃ k : Fin 3, i ≠ k ∧ j ≠ k ∧ ∀ l : Fin 3, l = i ∨ l = j ∨ l = k := by
    decide +kernel
  exact table i j h

theorem vector_three_bijective {i j k : Fin 3} (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k) :
    Function.Bijective (![i, j, k] : Fin 3 → Fin 3) := by
  have inj : Function.Injective (![i, j, k] : Fin 3 → Fin 3) := by
    have table : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
        ∀ a b : Fin 3, (![i, j, k] : Fin 3 → Fin 3) a = ![i, j, k] b → a = b := by
      decide +kernel
    exact fun _ _ => table i j k ij ik jk _ _
  exact Finite.injective_iff_bijective.mp inj

/-- A permutation of the three distinct labels preserves independence and the range. -/
theorem permuted_triangle_corners {v : Fin 3 → Space} (independent : LinearIndependent ℝ v)
    {i j k : Fin 3} (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k) :
    LinearIndependent ℝ ![v i, v j, v k] ∧
      Set.range (![v i, v j, v k] : Fin 3 → Space) = Set.range v := by
  have permutation := vector_three_bijective ij ik jk
  have eq : (![v i, v j, v k] : Fin 3 → Space) = v ∘ ![i, j, k] := by
    funext l
    fin_cases l <;> rfl
  rw [eq]
  exact ⟨independent.comp _ permutation.1, permutation.2.range_comp _⟩

end Unfoldings
