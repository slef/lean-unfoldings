module

public import Unfoldings.Topology.FiniteMonotoneSelection
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Tactic.Ring

/-! A continuous finite affine selection preserves a linear order along a segment. -/

@[expose] public section

namespace Unfoldings

theorem finite_affine_selection_segment_order {E V ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
    (A : ι → E →ᵃ[ℝ] V) (continuous : ∀ i, Continuous (A i))
    (L : V →L[ℝ] ℝ) {p q : E} {value : E → V}
    (value_continuous : ContinuousOn value (segment ℝ p q))
    (selection : ∀ z ∈ segment ℝ p q, ∃ i, value z = A i z)
    (increments : ∀ i, 0 ≤ L ((A i).linear (q - p))) : L (value p) ≤ L (value q) := by
  let P := Path.segment p q
  have inside (s : unitInterval) : P s ∈ segment ℝ p q :=
    lineMap_mem_segment ℝ _ _ s.property
  have formula (i : ι) (s : unitInterval) :
      L (A i (P s)) = (1 - (s : ℝ)) * L (A i p) + (s : ℝ) * L (A i q) := by
    change L (A i (AffineMap.lineMap p q (s : ℝ))) = _
    rw [(A i).apply_lineMap]
    simp only [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul]
    ring
  have monotone (i : ι) : Monotone (fun s : unitInterval => L (A i (P s))) := by
    intro s r ordered
    have linear : (A i).linear (q - p) = A i q - A i p := (A i).linear_apply_vsub q p
    have increment := increments i
    rw [linear, map_sub] at increment
    change L (A i (P s)) ≤ L (A i (P r))
    rw [formula, formula]
    nlinarith [mul_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ r from ordered)) increment]
  have bound := finite_monotone_selection_endpoints (fun i s => L (A i (P s)))
    (fun i => L.continuous.comp ((continuous i).comp P.continuous)) monotone
    (fun s => L (value (P s)))
    (L.continuous.comp (value_continuous.comp_continuous P.continuous inside))
    (fun s => (selection (P s) (inside s)).imp (fun _ equal => congrArg L equal))
  simpa only [Path.source, Path.target] using bound

end Unfoldings
