module

public import Unfoldings.Geometry.RadialPolarVariation
public import Unfoldings.Geometry.ChainInterval
public import Unfoldings.Geometry.WeightedHeadingBudget

/-! Actual link polar variations satisfy the finite radial-block summation hypotheses. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain ℂ n)

/-- The short angular sweep along one outward straight link, including a source-starting link. -/
def polarVariation (source : ℂ) (i : Fin n) : ℝ :=
  |((P.vertex i.succ - source) / (P.vertex i.castSucc - source)).arg|

theorem polarVariation_nonnegative (source : ℂ) (i : Fin n) : 0 ≤ P.polarVariation source i :=
  abs_nonneg _

theorem polarVariation_weighted_bound (source : ℂ) {γ : ℝ} (nonnegative : 0 ≤ γ)
    (small : γ ≤ 1) (i : Fin n)
    (progress : γ * (‖P.vertex i.castSucc - source‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - source) (P.edge i)) :
    ‖P.vertex i.castSucc - source‖ * P.polarVariation source i ≤
      Real.sqrt (1 - γ ^ 2) * ‖P.edge i‖ := by
  have estimate := radial_polar_step_bound' (P.vertex i.castSucc - source) (P.edge i)
    nonnegative small progress
  have endpoint : P.vertex i.castSucc - source + P.edge i = P.vertex i.succ - source := by
    unfold edge
    abel
  rw [endpoint] at estimate
  exact estimate

/-- The discrete Fubini prefix is the exact original prefix length. -/
theorem earlierLength_eq_interval_length (j : Fin n) :
    earlierLength (fun i => ‖P.edge i‖) j = (P.interval 0 j.val (by omega)).projectedLength := by
  classical
  unfold earlierLength projectedLength
  apply Finset.sum_bij (fun i hi => (⟨i.val, by
    exact (Finset.mem_filter.mp hi).2⟩ : Fin j.val))
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi k hk equal
    apply Fin.ext
    exact congrArg (fun z : Fin j.val => z.val) equal
  · intro k _
    let i : Fin n := ⟨k.val, by omega⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩, Fin.ext rfl⟩
  · intro i hi
    rw [P.interval_edge]
    congr 2
    apply Fin.ext
    simp only [Nat.zero_add]

/-- Radial progress and true prefix lengths bound all later polar winding with length weights. -/
theorem weighted_polarVariation_bound (source : ℂ) {γ C : ℝ}
    (constant : 0 ≤ C) (nonnegative : 0 ≤ γ) (small : γ ≤ 1)
    (margin : ∀ i, γ * (‖P.vertex i.castSucc - source‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - source) (P.edge i))
    (prefix_bound : ∀ j : Fin n, (P.interval 0 j.val (by omega)).projectedLength ≤
      C * ‖P.vertex j.castSucc - source‖) :
    (∑ i, ‖P.edge i‖ * futureVariation (P.polarVariation source) i) ≤
      C * Real.sqrt (1 - γ ^ 2) * P.projectedLength := by
  apply weighted_futureVariation_le (fun i => ‖P.edge i‖) (P.polarVariation source)
    (fun i => ‖P.vertex i.castSucc - source‖) constant (P.polarVariation_nonnegative source)
  · intro j
    rw [P.earlierLength_eq_interval_length]
    exact prefix_bound j
  · intro j
    exact P.polarVariation_weighted_bound source nonnegative small j (margin j)

end Unfoldings.PolygonalChain
