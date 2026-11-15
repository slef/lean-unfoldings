module

public import Unfoldings.Geometry.HeadingSubhistoryMargin
public import Unfoldings.Geometry.PolygonalRayOpening
public import Unfoldings.Geometry.RadialRayVertices

/-! Actual opening budgets supply strict outward progress at every genuine internal bank bend. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalRay

open PolygonalChain

variable {n : ℕ} (R : PolygonalRay ℂ n)

/-- Actual suffix rotations preserve every original genuine edge. -/
theorem openings_genuine (events : List (Opening n))
    (genuine : ∀ i : Fin n, R.chain.vertex i.castSucc ≠ R.chain.vertex i.succ)
    (i : Fin n) : (R.openings events).chain.vertex i.castSucc ≠
      (R.openings events).chain.vertex i.succ := by
  have original : R.chain.edge i ≠ 0 := sub_ne_zero.mpr (genuine i).symm
  have edge_nonzero : (R.openings events).chain.edge i ≠ 0 := by
    rw [R.openings_chain, R.chain.openings_edge]
    exact mul_ne_zero (polarRay_ne_zero _) original
  intro equal
  exact edge_nonzero (by rw [PolygonalChain.edge, equal, sub_self])

/-- The original subhistory estimates retain a strictly positive source-relative inner
product at every internal outgoing edge throughout the actual opening history. -/
theorem openings_initial_edge_inner_pos (events : List (Opening n)) {D d : ℝ}
    (constant : 0 ≤ D) (budget : D * openingBudget events < d)
    (length_bound : ∀ (j : Fin (n + 1)) (i : Fin n) (earlier : j.val ≤ i.val),
      (R.chain.interval j.val (i.val - j.val) (by omega)).projectedLength ≤
        D * ‖R.chain.vertex i.castSucc - R.chain.vertex j‖)
    (margin : ∀ (j : Fin (n + 1)) (i : Fin n), j.val ≤ i.val →
      d * (‖R.chain.vertex i.castSucc - R.chain.vertex j‖ * ‖R.chain.edge i‖) ≤
        inner ℝ (R.chain.vertex i.castSucc - R.chain.vertex j) (R.chain.edge i))
    (genuine : ∀ i : Fin n, R.chain.vertex i.castSucc ≠ R.chain.vertex i.succ)
    (radial : (R.openings events).Outward) (i : Fin n) (later : 0 < i.val) :
    0 < inner ℝ ((R.openings events).chain.vertex i.castSucc - (R.openings events).start)
      ((R.openings events).chain.edge i) := by
  have current_genuine := R.openings_genuine events genuine
  have estimate := R.chain.radial_margin_of_heading_oscillation (R.chain.openings events)
    (openingHeading events) (R.chain.openings_edge events) (openingBudget_nonneg events)
    constant budget (openingHeading_oscillation events) length_bound margin 0 i (Nat.zero_le _)
  rw [← R.openings_chain] at estimate
  have coefficient : 0 < (d - D * openingBudget events) / (1 + D * openingBudget events) :=
    div_pos (sub_pos.mpr budget)
      (by nlinarith [mul_nonneg constant (openingBudget_nonneg events)])
  have not_source : (R.openings events).chain.vertex i.castSucc ≠ (R.openings events).start := by
    intro equal
    have index := (R.openings events).vertex_injective_of_outward radial current_genuine equal
    have zero : i.val = 0 := congrArg Fin.val index
    omega
  have genuine_edge : (R.openings events).chain.edge i ≠ 0 :=
    sub_ne_zero.mpr (current_genuine i).symm
  have positive : 0 < ((d - D * openingBudget events) / (1 + D * openingBudget events)) *
      (‖(R.openings events).chain.vertex i.castSucc - (R.openings events).start‖ *
        ‖(R.openings events).chain.edge i‖) :=
    mul_pos coefficient (mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr not_source))
      (norm_pos_iff.mpr genuine_edge))
  exact positive.trans_le estimate

end Unfoldings.PolygonalRay
