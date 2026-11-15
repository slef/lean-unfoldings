module

public import Unfoldings.Geometry.OpeningPrefixBudget
public import Unfoldings.Geometry.PolygonalRaySuffix

/-! Uniform subhistory estimates keep every actual opened bank outward from all its hinges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

/-- Public index bounds keep interval hypotheses usable across module boundaries. -/
theorem interval_between_fits {n : ℕ} (j : Fin (n + 1)) (i : Fin n) (before : j.val ≤ i.val) :
    j.val + (i.val - j.val) ≤ n := by omega

theorem interval_tail_fits {n : ℕ} (j : Fin (n + 1)) : j.val + (n - j.val) ≤ n := by omega

end Unfoldings.PolygonalChain

namespace Unfoldings.PolygonalRay

open PolygonalChain

variable {n : ℕ} (R : PolygonalRay ℂ n) (events : List (Opening n)) {D d : ℝ}
  (constant : 0 ≤ D) (small : D * openingBudget events < d)
  (length_bound : ∀ (j : Fin (n + 1)) (i : Fin n) (earlier : j.val ≤ i.val),
    (R.chain.interval j.val (i.val - j.val) (interval_between_fits j i earlier)).projectedLength ≤
      D * ‖R.chain.vertex i.castSucc - R.chain.vertex j‖)
  (margin : ∀ (j : Fin (n + 1)) (i : Fin n), j.val ≤ i.val →
    d * (‖R.chain.vertex i.castSucc - R.chain.vertex j‖ * ‖R.chain.edge i‖) ≤
      inner ℝ (R.chain.vertex i.castSucc - R.chain.vertex j) (R.chain.edge i))
  (tail_length : ∀ j : Fin (n + 1),
    (R.chain.interval j.val (n - j.val) (interval_tail_fits j)).projectedLength ≤
      D * ‖R.chain.vertex (Fin.last n) - R.chain.vertex j‖)
  (tail_margin : ∀ j : Fin (n + 1),
    d * (‖R.chain.vertex (Fin.last n) - R.chain.vertex j‖ * ‖R.direction‖) ≤
      inner ℝ (R.chain.vertex (Fin.last n) - R.chain.vertex j) R.direction)

include constant small length_bound margin in
theorem openings_chain_outward : (R.openings events).chain.Outward := by
  rw [R.openings_chain]
  exact R.chain.outward_of_heading_oscillation (R.chain.openings events)
    (openingHeading events) (R.chain.openings_edge events) (openingBudget_nonneg events)
    constant small (openingHeading_oscillation events) length_bound margin

include constant small tail_length tail_margin in
/-- The actual infinite tail points away from every retained current hinge. -/
theorem openings_tail_outward_from (j : Fin (n + 1)) :
    0 ≤ inner ℝ ((R.openings events).chain.vertex (Fin.last n) -
      (R.openings events).chain.vertex j) (R.openings events).direction := by
  let A := R.chain.interval j.val (n - j.val) (by omega)
  let B := (R.openings events).chain.interval j.val (n - j.val) (by omega)
  let correction (i : Fin (n - j.val)) := openingHeading events ⟨j.val + i.val, by omega⟩
  have edges (i : Fin (n - j.val)) : B.edge i = polarRay (correction i) * A.edge i := by
    change ((R.openings events).chain.interval j.val (n - j.val) _).edge i = _
    rw [interval_edge, R.openings_chain, R.chain.openings_edge]
    rfl
  have first : (⟨j.val, by omega⟩ : Fin (n + 1)) = j := Fin.ext rfl
  have last : (⟨j.val + (n - j.val), by omega⟩ : Fin (n + 1)) = Fin.last n :=
    Fin.ext (by simp only [Fin.val_last]; omega)
  have endpointA : A.vertex (Fin.last (n - j.val)) - A.vertex 0 =
      R.chain.vertex (Fin.last n) - R.chain.vertex j := by
    change R.chain.vertex ⟨j.val + (n - j.val), by omega⟩ - R.chain.vertex ⟨j.val, by omega⟩ = _
    rw [first, last]
  have endpointB : B.vertex (Fin.last (n - j.val)) - B.vertex 0 =
      (R.openings events).chain.vertex (Fin.last n) - (R.openings events).chain.vertex j := by
    change (R.openings events).chain.vertex ⟨j.val + (n - j.val), by omega⟩ -
      (R.openings events).chain.vertex ⟨j.val, by omega⟩ = _
    rw [first, last]
  have lengthA : A.projectedLength ≤ D * ‖A.vertex (Fin.last _) - A.vertex 0‖ := by
    rw [endpointA]
    exact tail_length j
  have marginA : d * (‖A.vertex (Fin.last _) - A.vertex 0‖ * ‖R.direction‖) ≤
      inner ℝ (A.vertex (Fin.last _) - A.vertex 0) R.direction := by
    rw [endpointA]
    exact tail_margin j
  have estimate := A.heading_radial_margin B correction edges (openingBudget_nonneg events)
    constant (fun i => openingHeading_tail_error events ⟨j.val + i.val, by omega⟩)
    small lengthA R.direction marginA
  rw [endpointB, ← R.openings_direction] at estimate
  have coefficient : 0 ≤ (d - D * openingBudget events) / (1 + D * openingBudget events) :=
    div_nonneg (sub_pos.mpr small).le
      (by nlinarith [mul_nonneg constant (openingBudget_nonneg events)])
  exact (mul_nonneg coefficient (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans estimate

include constant small length_bound margin tail_length tail_margin in
/-- Original subhistory estimates supply both whole-bank and all suffix radial hypotheses. -/
theorem openings_outward_and_suffixes : (R.openings events).Outward ∧
    ∀ hinge, ((R.openings events).suffix hinge).Outward := by
  have finite := R.openings_chain_outward events constant small length_bound margin
  have tail_test := R.openings_tail_outward_from events constant small tail_length tail_margin
  constructor
  · exact ⟨(fun i _ => ((R.openings events).chain.radiallyMonotone_iff_outward.mpr finite)
      0 i (Nat.zero_le _)), tail_test 0⟩
  · intro hinge
    exact (R.openings events).suffix_outward hinge finite (tail_test hinge)

end Unfoldings.PolygonalRay
