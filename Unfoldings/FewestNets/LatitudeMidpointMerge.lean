module

public import Unfoldings.FewestNets.LatitudeStripPartition
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Prod.Lex.Basic

/-! Sort the two rows' actual midpoints, advancing the upper row first at ties. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

/-- The longitude of the edge from index i to i + 1 in a row of size n. -/
def rowMidpoint (n : ℕ) (i : Fin n) : ℝ := 2 * π * ((i.val : ℝ) + 1 / 2) / n

theorem rowMidpoint_strictMono (n : ℕ) : StrictMono (rowMidpoint n) := by
  intro i j ordered
  have nonzero : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have vals : (i.val : ℝ) < j.val := by exact_mod_cast (show i.val < j.val from ordered)
  unfold rowMidpoint
  exact div_lt_div_of_pos_right
    (mul_lt_mul_of_pos_left (add_lt_add_left vals _) (by positivity)) nonzero

variable {lower upper : ℕ}

/-- A midpoint's key orders equal longitudes with the upper row first. -/
def midpointKey : Fin lower ⊕ Fin upper → ℝ ×ₗ ℕ
  | .inl i => toLex (rowMidpoint lower i, 1)
  | .inr i => toLex (rowMidpoint upper i, 0)

theorem midpointKey_injective : Function.Injective (midpointKey (lower := lower) (upper := upper)) := by
  intro a b same
  have time := congrArg (fun p : ℝ ×ₗ ℕ => (ofLex p).1) same
  have row := congrArg (fun p : ℝ ×ₗ ℕ => (ofLex p).2) same
  cases a with
  | inl i =>
    cases b with
    | inl j => exact congrArg Sum.inl ((rowMidpoint_strictMono lower).injective time)
    | inr j => simp [midpointKey] at row
  | inr i =>
    cases b with
    | inl j => simp [midpointKey] at row
    | inr j => exact congrArg Sum.inr ((rowMidpoint_strictMono upper).injective time)

/-- Each step advances one row by one edge, in the strict order of the tagged
midpoints. Counted with both tags, there are exactly lower + upper advances. -/
theorem exists_midpointOrder :
    ∃ step : Fin (lower + upper) ≃ (Fin lower ⊕ Fin upper),
      StrictMono (midpointKey ∘ step) := by
  classical
  let key : (Fin lower ⊕ Fin upper) ↪ ℝ ×ₗ ℕ := ⟨midpointKey, midpointKey_injective⟩
  let keys := Finset.univ.map key
  have card : keys.card = lower + upper := by simp [keys]
  have inverse (k : keys) : ∃ e : Fin lower ⊕ Fin upper, midpointKey e = k.val := by
    have present : k.val ∈ Finset.univ.map key := k.property
    obtain ⟨e, _, eq⟩ := Finset.mem_map.mp present
    exact ⟨e, eq⟩
  let decode : keys ≃ (Fin lower ⊕ Fin upper) :=
    { toFun := fun k => Classical.choose (inverse k)
      invFun := fun e => ⟨midpointKey e, Finset.mem_map.mpr ⟨e, Finset.mem_univ _, rfl⟩⟩
      left_inv := fun k => Subtype.ext (Classical.choose_spec (inverse k))
      right_inv := fun e => midpointKey_injective (Classical.choose_spec
        (inverse ⟨midpointKey e, Finset.mem_map.mpr ⟨e, Finset.mem_univ _, rfl⟩⟩)) }
  let sorted := keys.orderIsoOfFin card
  let step := sorted.toEquiv.trans decode
  have key_at (i) : midpointKey (step i) = keys.orderEmbOfFin card i :=
    (Classical.choose_spec (inverse (sorted i))).trans (keys.coe_orderIsoOfFin_apply card i)
  refine ⟨step, fun i j advance => ?_⟩
  show midpointKey (step i) < midpointKey (step j)
  rw [key_at, key_at]
  exact (keys.orderEmbOfFin card).strictMono advance

end Unfoldings.FewestNets
