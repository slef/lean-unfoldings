module

public import Unfoldings.Geometry.BankCornerTurn
public import Unfoldings.Geometry.OpeningStrictProgress
public import Unfoldings.Geometry.OpeningAllAnchors
public import Unfoldings.Geometry.RadialVertexCoordinates
public import Unfoldings.Geometry.RadialSubhistoryLength
public import Unfoldings.Geometry.TerminalEdgeRay

/-! Scaled openings preserve the real turn lift and give the exact change of gap aperture. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {n : ℕ}

/-- Scale each original angle while keeping each named hinge fixed. -/
def scaleOpenings (u : ℝ) (events : List (Opening n)) : List (Opening n) :=
  events.map (fun e => ⟨e.hinge, u * e.angle⟩)

theorem openingHeading_scaleOpenings (u : ℝ) (events : List (Opening n)) (i : Fin n) :
    openingHeading (scaleOpenings u events) i = u * openingHeading events i := by
  induction events with
  | nil => simp [scaleOpenings, openingHeading]
  | cons e events ih =>
    have next : (if e.hinge ≤ i.castSucc then u * e.angle else 0) =
        u * (if e.hinge ≤ i.castSucc then e.angle else 0) := by
      split_ifs <;> simp
    change (if e.hinge ≤ i.castSucc then u * e.angle else 0) +
      openingHeading (scaleOpenings u events) i = u *
        ((if e.hinge ≤ i.castSucc then e.angle else 0) + openingHeading events i)
    rw [next, ih, mul_add]

theorem openingBudget_scaleOpenings (u : ℝ) (events : List (Opening n)) :
    openingBudget (scaleOpenings u events) = |u| * openingBudget events := by
  induction events with
  | nil => simp [scaleOpenings, openingBudget]
  | cons e events ih =>
    change |u * e.angle| + openingBudget (scaleOpenings u events) =
      |u| * (|e.angle| + openingBudget events)
    rw [abs_mul, ih, mul_add]

@[simp]
theorem scaleOpenings_one (events : List (Opening n)) : scaleOpenings 1 events = events := by
  unfold scaleOpenings
  have identity : (fun e : Opening n => (⟨e.hinge, 1 * e.angle⟩ : Opening n)) = id := by
    funext event
    cases event
    simp
  rw [identity, List.map_id]

end Unfoldings.PolygonalChain

namespace Unfoldings.PolygonalRay

open PolygonalChain

variable {n : ℕ} (R : PolygonalRay ℂ (n + 2)) (events : List (Opening (n + 2))) {D d : ℝ}
  (constant : 0 ≤ D) (small : D * openingBudget events < d)
  (length_bound : ∀ (j : Fin (n + 3)) (i : Fin (n + 2)) (before : j.val ≤ i.val),
    (R.chain.interval j.val (i.val - j.val) (interval_between_fits j i before)).projectedLength ≤
      D * ‖R.chain.vertex i.castSucc - R.chain.vertex j‖)
  (margin : ∀ (j : Fin (n + 3)) (i : Fin (n + 2)), j.val ≤ i.val →
    d * (‖R.chain.vertex i.castSucc - R.chain.vertex j‖ * ‖R.chain.edge i‖) ≤
      inner ℝ (R.chain.vertex i.castSucc - R.chain.vertex j) (R.chain.edge i))
  (tail_length : ∀ j : Fin (n + 3),
    (R.chain.interval j.val (n + 2 - j.val) (interval_tail_fits j)).projectedLength ≤
      D * ‖R.chain.vertex (Fin.last (n + 2)) - R.chain.vertex j‖)
  (tail_margin : ∀ j : Fin (n + 3),
    d * (‖R.chain.vertex (Fin.last (n + 2)) - R.chain.vertex j‖ * ‖R.direction‖) ≤
      inner ℝ (R.chain.vertex (Fin.last (n + 2)) - R.chain.vertex j) R.direction)
  (genuine : ∀ i : Fin (n + 2), R.chain.vertex i.castSucc ≠ R.chain.vertex i.succ)

local notation "Radius[" B "," k "]" =>
  PolygonalChain.vertex (PolygonalRay.chain B) (Fin.castSucc (Fin.succ k)) -
    PolygonalRay.start B
local notation "Incoming[" B "," k "]" =>
  PolygonalChain.edge (PolygonalRay.chain B) (Fin.castSucc k)
local notation "Outgoing[" B "," k "]" => PolygonalChain.edge (PolygonalRay.chain B) (Fin.succ k)

include constant small length_bound margin tail_length tail_margin genuine in
/-- Both incident edge bearings remain strictly radial after scaling every actual opening. -/
theorem openings_scaled_corner_radial (u : ℝ) (bounds : u ∈ Set.Icc (0 : ℝ) 1)
    (k : Fin (n + 1)) :
    let Q := R.openings (scaleOpenings u events)
    0 < inner ℝ Radius[Q,k] Incoming[Q,k] ∧ 0 < inner ℝ Radius[Q,k] Outgoing[Q,k] := by
  let scaled := scaleOpenings u events
  let Q := R.openings scaled
  have scaled_small : D * openingBudget scaled < d := by
    change D * openingBudget (scaleOpenings u events) < d
    rw [openingBudget_scaleOpenings, abs_of_nonneg bounds.1]
    exact (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (openingBudget_nonneg events)
      bounds.2) constant).trans_lt small
  have radial := (R.openings_outward_and_suffixes scaled constant scaled_small length_bound
    margin tail_length tail_margin).1
  have inc := Q.inner_terminal_edge_pos radial k.castSucc
    (R.openings_genuine scaled genuine k.castSucc)
  have out := R.openings_initial_edge_inner_pos scaled constant scaled_small length_bound
    margin genuine radial k.succ (Nat.succ_pos _)
  exact ⟨by simpa only [PolygonalChain.edge, Fin.succ_castSucc] using inc, out⟩

include genuine margin in
/-- The all-anchor margin is strict along an outgoing edge at a genuine interior bend. -/
theorem corner_outgoing_radial (outward : R.Outward) (positive : 0 < d) (k : Fin (n + 1)) :
    0 < inner ℝ Radius[R,k] Outgoing[R,k] := by
  have center : R.chain.vertex k.succ.castSucc ≠ R.start := by
    intro h
    have zero := R.vertex_injective_of_outward outward genuine h
    exact (Nat.succ_ne_zero _) (congrArg Fin.val zero)
  have edge : R.chain.edge k.succ ≠ 0 := sub_ne_zero.mpr (genuine k.succ).symm
  exact (mul_pos positive (mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr center))
    (norm_pos_iff.mpr edge))).trans_le (margin 0 k.succ (Nat.zero_le _))

include constant small length_bound margin tail_length tail_margin genuine in
/-- At an interior finite-bank bend the two occupied gap apertures sum to one full turn
plus the new forward turn. This uses the exact real opening headings, with no wrap premise. -/
theorem openings_corner_widths_add (outward : R.Outward) (k : Fin (n + 1)) :
    let Q := R.openings events
    radialLeftCornerWidth Radius[R,k] Incoming[R,k] Outgoing[R,k] +
      radialRightCornerWidth Radius[Q,k] Incoming[Q,k] Outgoing[Q,k] =
        2 * Real.pi + (openingHeading events k.succ - openingHeading events k.castSucc) := by
  let Q := R.openings events
  let a := openingHeading events k.castSucc
  let b := openingHeading events k.succ
  have first : 0 < inner ℝ Radius[R,k] Incoming[R,k] := by
    simpa only [PolygonalChain.edge, Fin.succ_castSucc] using
      R.inner_terminal_edge_pos outward k.castSucc (genuine k.castSucc)
  have dpos : 0 < d := lt_of_le_of_lt
    (mul_nonneg constant (openingBudget_nonneg events)) small
  have last := R.corner_outgoing_radial margin genuine outward dpos k
  have bearings (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) : ∃ r : ℂ,
      0 < inner ℝ r (polarRay (u * a) * Incoming[R,k]) ∧
        0 < inner ℝ r (polarRay (u * b) * Outgoing[R,k]) := by
    let A := R.openings (scaleOpenings u events)
    have radial := R.openings_scaled_corner_radial events constant small length_bound margin
      tail_length tail_margin genuine u hu k
    refine ⟨Radius[A,k], ?_⟩
    have inc : Incoming[A,k] = polarRay (u * a) * Incoming[R,k] := by
      simp only [A, openings_chain, openings_edge, openingHeading_scaleOpenings, a]
    have out : Outgoing[A,k] = polarRay (u * b) * Outgoing[R,k] := by
      simp only [A, openings_chain, openings_edge, openingHeading_scaleOpenings, b]
    exact ⟨inc ▸ radial.1, out ▸ radial.2⟩
  have strict : 0 < inner ℝ Radius[Q,k] Incoming[Q,k] ∧
      0 < inner ℝ Radius[Q,k] Outgoing[Q,k] := by
    have radial := R.openings_scaled_corner_radial events constant small length_bound margin
      tail_length tail_margin genuine 1 (by constructor <;> norm_num) k
    simpa only [scaleOpenings_one] using radial
  have inc : Incoming[Q,k] = polarRay a * Incoming[R,k] := by
    exact (congrArg (fun P => P.edge k.castSucc) (R.openings_chain events)).trans
      (R.chain.openings_edge events _)
  have out : Outgoing[Q,k] = polarRay b * Outgoing[R,k] := by
    exact (congrArg (fun P => P.edge k.succ) (R.openings_chain events)).trans
      (R.chain.openings_edge events _)
  dsimp only
  rw [radialLeftCornerWidth_eq_pi_sub_turn, radialRightCornerWidth_eq_pi_add_turn]
  change Real.pi - radialBankTurn Radius[R,k] Incoming[R,k] Outgoing[R,k] +
    (Real.pi + radialBankTurn Radius[Q,k] Incoming[Q,k] Outgoing[Q,k]) = 2 * Real.pi + (b - a)
  rw [inc, out]
  have change_turn := radialBankTurn_rotation_of_intermediate_radial Radius[R,k] Radius[Q,k]
    Incoming[R,k] Outgoing[R,k] a b first last (inc ▸ strict.1) (out ▸ strict.2) bearings
  rw [change_turn]
  ring

end Unfoldings.PolygonalRay

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain ℂ (n + 1))

/-- The original margin and small curvature budget give the occupied apertures at each
interior bend of the canonical terminal-edge continuation. -/
theorem terminalEdge_openings_corner_geometry (events : List (Opening (n + 1)))
    (genuine : ∀ i : Fin (n + 1), P.vertex i.castSucc ≠ P.vertex i.succ)
    (outward : P.terminalEdgeRay.Outward) {γ : ℝ} (positive : 0 < γ) (small : γ ≤ 1)
    (budget : 3 * openingBudget events < γ ^ 2)
    (margin : ∀ (j : Fin (n + 2)) (i : Fin (n + 1)), j.val ≤ i.val →
      γ * (‖P.vertex i.castSucc - P.vertex j‖ * ‖P.edge i‖) ≤
        inner ℝ (P.vertex i.castSucc - P.vertex j) (P.edge i)) (k : Fin n) :
    let R := P.terminalEdgeRay
    let Q := R.openings events
    let r := R.chain.vertex k.succ.castSucc - R.start
    let q := Q.chain.vertex k.succ.castSucc - Q.start
    0 < inner ℝ r (R.chain.edge k.succ) ∧
    0 < inner ℝ q (Q.chain.edge k.succ) ∧
    radialLeftCornerWidth r (R.chain.edge k.castSucc) (R.chain.edge k.succ) +
      radialRightCornerWidth q (Q.chain.edge k.castSucc) (Q.chain.edge k.succ) =
        2 * Real.pi + (openingHeading events k.succ - openingHeading events k.castSucc) := by
  cases n with
  | zero => exact k.elim0
  | succ n =>
    let R := P.terminalEdgeRay
    have radial_budget : γ⁻¹ * openingBudget events < γ := by
      have bound : openingBudget events < γ * γ := by
        nlinarith [openingBudget_nonneg events]
      have estimate := mul_lt_mul_of_pos_left bound (inv_pos.mpr positive)
      rwa [← mul_assoc, inv_mul_cancel₀ positive.ne', one_mul] at estimate
    have constant := inv_nonneg.mpr positive.le
    have lengths := P.subhistory_length_between positive small margin
    have tail_lengths := P.subhistory_length_tail positive small margin
    have tail_margin := P.terminalEdgeRay_tail_margin positive.le small margin
    have scaled := R.openings_scaled_corner_radial events constant radial_budget lengths margin
      tail_lengths tail_margin genuine 1 (by constructor <;> norm_num) k
    rw [scaleOpenings_one] at scaled
    exact ⟨R.corner_outgoing_radial margin genuine outward positive k, scaled.2,
      R.openings_corner_widths_add events constant radial_budget lengths margin
        tail_lengths tail_margin genuine outward k⟩

end Unfoldings.PolygonalChain
