module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.UnitInterval
public import Mathlib.Tactic.Linarith

/-! A continuous selection from finitely many monotone functions preserves endpoint order. -/

@[expose] public section

namespace Unfoldings

open Filter Topology

/-- Near a given parameter, a continuous finite selection can only use branches which agree
with it at that parameter. The branch may change arbitrarily often nearby. -/
theorem finite_selection_eventually_active {ι : Type*} [Finite ι]
    (branch : ι → unitInterval → ℝ) (branch_continuous : ∀ i, Continuous (branch i))
    (selected : unitInterval → ℝ) (selected_continuous : Continuous selected)
    (t : unitInterval) :
    ∀ᶠ s in 𝓝 t, ∀ i, selected s = branch i s → selected t = branch i t := by
  rw [Filter.eventually_all]
  intro i
  by_cases active : selected t = branch i t
  · exact Filter.Eventually.of_forall (fun _ _ => active)
  · have different : ∀ᶠ s in 𝓝 t, selected s ≠ branch i s :=
      (isOpen_ne_fun selected_continuous (branch_continuous i)).mem_nhds active
    exact different.mono (fun _ unequal equal => (unequal equal).elim)

/-- A continuous selection from a finite family of continuous monotone functions cannot
decrease between the interval endpoints. No bound on the number of branch changes is assumed. -/
theorem finite_monotone_selection_endpoints {ι : Type*} [Finite ι]
    (branch : ι → unitInterval → ℝ) (branch_continuous : ∀ i, Continuous (branch i))
    (branch_monotone : ∀ i, Monotone (branch i))
    (selected : unitInterval → ℝ) (selected_continuous : Continuous selected)
    (selection : ∀ t, ∃ i, selected t = branch i t) : selected 0 ≤ selected 1 := by
  let good : Set unitInterval := {t | selected 0 ≤ selected t}
  have closed : IsClosed good := isClosed_le continuous_const selected_continuous
  have reaches : Set.Icc (0 : unitInterval) 1 ⊆ good := by
    apply (closed.inter isClosed_Icc).Icc_subset_of_forall_mem_nhdsWithin
      (show (0 : unitInterval) ∈ good from le_refl (selected 0))
    intro t member
    have active := finite_selection_eventually_active branch branch_continuous selected
      selected_continuous t
    filter_upwards [active.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin (s := Set.Ioi t)] with s active later
    obtain ⟨i, at_s⟩ := selection s
    change selected 0 ≤ selected s
    have previous : selected 0 ≤ selected t := member.1
    exact previous.trans (by
      rw [active i at_s, at_s]
      exact branch_monotone i later.le)
  exact reaches ⟨zero_le_one, le_rfl⟩

/-- A common quantitative coordinate bound passes through a continuous finite selection. -/
theorem finite_selection_coordinate_bound {ι : Type*} [Finite ι]
    (input selected : unitInterval → ℝ) (input_continuous : Continuous input)
    (selected_continuous : Continuous selected) (c : ℝ)
    (branch : ι → unitInterval → ℝ) (branch_continuous : ∀ i, Continuous (branch i))
    (branch_bound : ∀ i, Monotone (fun t => branch i t - c * input t))
    (selection : ∀ t, ∃ i, selected t = branch i t) :
    c * (input 1 - input 0) ≤ selected 1 - selected 0 := by
  have order := finite_monotone_selection_endpoints
    (fun i t => branch i t - c * input t)
    (fun i => (branch_continuous i).sub (continuous_const.mul input_continuous)) branch_bound
    (fun t => selected t - c * input t)
    (selected_continuous.sub (continuous_const.mul input_continuous))
    (fun t => (selection t).imp (fun _ same => congrArg (fun r => r - c * input t) same))
  linarith

end Unfoldings
