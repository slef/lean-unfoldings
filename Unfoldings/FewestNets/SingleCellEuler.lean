module

public import Unfoldings.FewestNets.SingleCellCharge
public import Unfoldings.Combinatorics.ComponentEulerAccounting

/-! Linearize the Euler count of one induced Gaussian subcomplex. -/

@[expose] public section

namespace Unfoldings.FewestNets.SingleCellCharge

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]

/-- A binary membership flag viewed as a real indicator. -/
def membershipValue (inside : Bool) : ℝ := if inside then 1 else 0

private theorem both_endpoints (a b : Bool) :
    2 * membershipValue (a && b) = endpoints (a, b) - crossing (a, b) := by
  cases a <;> cases b <;> norm_num [membershipValue, crossing, endpoints]

/-- The pointwise Euler expression for a single selection is exactly its
signed polygon charges plus a linear combination of vertex memberships.
Each side is counted twice, including degenerate seams. -/
theorem binary_euler_linearization [DecidableEq E]
    (left right : E → V) (sides : F → Finset E) (marked₀ marked₁ : F → E)
    (twice : ∀ e, (Finset.univ.filter fun f => e ∈ sides f).card = 2)
    (selected : V → Bool) (full : F → Bool) :
    let edge (e : E) := (selected (left e), selected (right e))
    let changes (f : F) := ∑ e ∈ sides f, crossing (edge e)
    (∑ v, membershipValue (selected v)) -
      (∑ e, membershipValue ((selected (left e)) && (selected (right e)))) +
      (∑ f, membershipValue (full f)) =
    (∑ v, membershipValue (selected v)) - (∑ e, endpoints (edge e)) / 2 +
      (∑ f, (endpoints (edge (marked₀ f)) + endpoints (edge (marked₁ f)))) / 4 +
      ∑ f, charge (changes f) (edge (marked₀ f)) (edge (marked₁ f)) (full f) := by
  classical
  let edge (e : E) := (selected (left e), selected (right e))
  let changes (f : F) := ∑ e ∈ sides f, crossing (edge e)
  let changed (e : E) := selected (left e) ≠ selected (right e)
  have indicator (e : E) : crossing (edge e) = if changed e then (1 : ℝ) else 0 := by
    by_cases h : changed e
    · simp [edge, changed, crossing, h]
    · simp only [changed, ne_eq, not_not] at h
      simp [edge, changed, crossing, h]
  have sum_indicator (s : Finset E) :
      (∑ e ∈ s, crossing (edge e)) = ((s.filter changed).card : ℝ) := by
    simp only [indicator]
    have count : (∑ e ∈ s, if changed e then (1 : ℕ) else 0) = (s.filter changed).card :=
      Finset.sum_boole _ _
    exact_mod_cast count
  have incidences : (∑ f, changes f) = 2 * ∑ e, crossing (edge e) := by
    have counts : (∑ f, ((sides f |>.filter changed).card : ℝ)) =
        2 * ((Finset.univ.filter changed).card : ℝ) := by
      exact_mod_cast sum_card_filtered_sides sides changed twice
    simpa only [changes, sum_indicator] using counts
  have edge_total :
      2 * (∑ e : E, membershipValue (selected (left e) && selected (right e))) =
        (∑ e, endpoints (edge e)) - (∑ e, crossing (edge e)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun e _ => both_endpoints (selected (left e)) (selected (right e)))
  dsimp only
  simp only [charge, membershipValue, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div]
  simp only [edge, membershipValue] at edge_total
  simp only [changes, edge] at incidences
  have marked : (∑ f, (endpoints (edge (marked₀ f)) + endpoints (edge (marked₁ f)))) =
      (∑ f, endpoints (edge (marked₀ f))) + (∑ f, endpoints (edge (marked₁ f))) := by
    rw [Finset.sum_add_distrib]
  simp only [edge] at marked
  linarith only [incidences, edge_total, marked]

end Unfoldings.FewestNets.SingleCellCharge
