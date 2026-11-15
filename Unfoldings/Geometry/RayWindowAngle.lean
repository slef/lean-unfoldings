module

public import Unfoldings.Geometry.LocalHeadingBudget
public import Unfoldings.Geometry.ChainPolarVariation
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-! Source-ray directions between the terminal links of a short actual polar window. -/

@[expose] public section

namespace Unfoldings

/-- Triangle inequalities control every actual subinterval by the difference of its angular sums. -/
theorem angle_le_partialSum_difference {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {n : ℕ} (ray : Fin (n + 1) → E) (genuine : ∀ i, ray i ≠ 0)
    {i j : Fin (n + 1)} (ordered : i ≤ j) :
    InnerProductGeometry.angle (ray i) (ray j) ≤
      Fin.partialSum (fun k => InnerProductGeometry.angle (ray k.castSucc) (ray k.succ)) j -
        Fin.partialSum (fun k => InnerProductGeometry.angle (ray k.castSucc) (ray k.succ)) i := by
  have bound (j : Fin (n + 1)) : ∀ i ≤ j, InnerProductGeometry.angle (ray i) (ray j) ≤
      Fin.partialSum (fun k => InnerProductGeometry.angle (ray k.castSucc) (ray k.succ)) j -
        Fin.partialSum (fun k => InnerProductGeometry.angle (ray k.castSucc) (ray k.succ)) i := by
    refine Fin.induction ?_ (fun k previous => ?_) j
    · intro i before
      have equal : i = 0 := le_antisymm before (Fin.zero_le _)
      rw [equal, InnerProductGeometry.angle_self (genuine 0), sub_self]
    · intro i before
      by_cases equal : i = k.succ
      · rw [equal, InnerProductGeometry.angle_self (genuine k.succ), sub_self]
      · have earlier : i ≤ k.castSucc := by
          change i.val ≤ k.val
          have bound : i.val ≤ k.val + 1 := before
          have different : i.val ≠ k.val + 1 := fun same => equal (Fin.ext same)
          omega
        have prefix_bound := previous i earlier
        have triangle := InnerProductGeometry.angle_le_angle_add_angle (ray i) (ray k.castSucc)
          (ray k.succ)
        rw [Fin.partialSum_succ]
        linarith
  exact bound j i ordered

namespace PolygonalChain

variable {n : ℕ} (P : PolygonalChain ℂ n) (source : ℂ)

/-- Interior polar variation bounds the angle from the first link's far ray to the last. -/
theorem source_ray_angle_le_interiorVariation
    (genuine : ∀ i, P.vertex i - source ≠ 0) {i j : Fin n} (ordered : i < j) :
    InnerProductGeometry.angle (P.vertex i.succ - source) (P.vertex j.castSucc - source) ≤
      interiorVariation (P.polarVariation source) i j := by
  let ray (k : Fin (n + 1)) := P.vertex k - source
  have before : i.succ ≤ j.castSucc := by change i.val + 1 ≤ j.val; exact ordered
  have bound := angle_le_partialSum_difference ray genuine before
  have angle (k : Fin n) : InnerProductGeometry.angle (ray k.castSucc) (ray k.succ) =
      P.polarVariation source k := by
    rw [InnerProductGeometry.angle_comm,
      Complex.angle_eq_abs_arg (genuine k.succ) (genuine k.castSucc)]
    rfl
  simp_rw [angle] at bound
  have difference : Fin.partialSum (P.polarVariation source) j.castSucc -
      Fin.partialSum (P.polarVariation source) i.succ =
        interiorVariation (P.polarVariation source) i j := by
    classical
    simp only [Fin.partialSum, List.sum_take_ofFn, Finset.sum_filter,
      ← Finset.sum_sub_distrib, interiorVariation, Fin.val_castSucc, Fin.val_succ]
    apply Finset.sum_congr rfl
    intro k _
    by_cases first : k.val < i.val + 1 <;> by_cases last : k.val < j.val
    · simp only [first, last, ite_true]
      rw [ite_eq_right (by change ¬ (i.val < k.val ∧ k.val < j.val); omega)]
      exact sub_self _
    · exact (last (by have ij : i.val < j.val := ordered; omega)).elim
    · rw [ite_eq_right first, ite_eq_left last,
        ite_eq_left (by change i.val < k.val ∧ k.val < j.val; omega), sub_zero]
    · rw [ite_eq_right first, ite_eq_right last,
        ite_eq_right (by change ¬ (i.val < k.val ∧ k.val < j.val); omega), sub_zero]
  rw [difference] at bound
  exact bound

end PolygonalChain
end Unfoldings
