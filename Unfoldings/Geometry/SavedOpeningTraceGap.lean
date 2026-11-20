module

public import Unfoldings.Geometry.HingeCircleVertexMargin
public import Unfoldings.Geometry.OpeningTraceSharpPhase
public import Unfoldings.Geometry.PositiveOpeningTraceGap

/-! The sharp saved-bank angular budget gives an actual complete polygonal gap. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

open PolygonalChain

variable {n : ℕ} (R : PolygonalRay ℂ n)

/-- Original subhistory estimates and the sharp angular budget give a complete gap
between a saved actual bank and its fresh positive opening. A saved budget of
`2 * Ω` and a fresh budget of `Ω` allow `ε = 3 * Ω`. -/
theorem exists_saved_opening_trace_gap
    (saved events : List (Opening n)) (nonzero : R.direction ≠ 0)
    (edges_ne : ∀ i, R.chain.edge i ≠ 0)
    {ε D d : ℝ} (constant : 0 ≤ D) (margin_le_one : d ≤ 1)
    (history_budget : openingBudget saved + openingBudget events ≤ ε)
    (radial_budget : D * ε < d)
    (angle_budget : (2 / ((d - D * ε) / (1 + D * ε))) * openingBudget events < Real.pi)
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
    (positive : ∀ k : Fin events.length, 0 < (events.get k).angle)
    (small : ∀ k : Fin events.length, (events.get k).angle < Real.pi)
    (first : Fin events.length) (source_hinge : (events.get first).hinge = 0) :
    ∃ G : Set ℂ,
      IsClosed G ∧
      frontier G = (R.openings saved).carrier ∪ (R.openings (saved ++ events)).carrier ∧
      (R.openings saved).carrier ∩ (R.openings (saved ++ events)).carrier = {R.start} ∧
      (interior G).Nonempty ∧ closure (interior G) = G ∧
      CompleteSpace (PolygonalPoint G) ∧ ContractibleSpace (PolygonalPoint G) ∧
      ∃ (I : Type) (_ : Fintype I) (cells : I → Set ℂ),
        (∀ i, IsClosed (cells i) ∧ Convex ℝ (cells i) ∧ (interior (cells i)).Nonempty) ∧
        (∀ i j, i ≠ j → Disjoint (interior (cells i)) (interior (cells j))) ∧
        G = ⋃ i, cells i := by
  let B := R.openings saved
  let m := (d - D * ε) / (1 + D * ε)
  have epsilon : 0 ≤ ε :=
    (add_nonneg (openingBudget_nonneg saved) (openingBudget_nonneg events)).trans history_budget
  have denominator : 0 < 1 + D * ε := by positivity
  have m_pos : 0 < m := div_pos (sub_pos.mpr radial_budget) denominator
  have m_le_one : m ≤ 1 := (div_le_one denominator).mpr
    (by linarith [mul_nonneg constant epsilon])
  have budget (word : List (Opening n)) (bound : openingBudget word ≤ openingBudget events) :
      openingBudget (saved ++ word) ≤ ε := by
    rw [openingBudget_append]
    exact (add_le_add_right bound (openingBudget saved)).trans history_budget
  have control (word : List (Opening n)) (bound : openingBudget word ≤ openingBudget events) :
      (B.openings word).Outward ∧ ∀ i, ((B.openings word).suffix i).Outward := by
    rw [← R.openings_append]
    exact R.openings_outward_and_suffixes (saved ++ word) constant
      ((mul_le_mul_of_nonneg_left (budget word bound) constant).trans_lt radial_budget)
      length_bound margin tail_length tail_margin
  have states (k : ℕ) : (B.openingPrefix events k).Outward :=
    (control (events.take k) (openingBudget_take_le events k)).1
  have sweeps (k : Fin events.length) (θ : Set.Icc 0 (events.get k).angle) :
      ((B.openingPrefix events k.val).rotateSuffix (events.get k).hinge θ.val).Outward := by
    let event : Opening n := ⟨(events.get k).hinge, θ.val⟩
    have actual := (control (events.take k.val ++ [event])
      (openingBudget_take_partial_le events k θ.val θ.property)).1
    rw [B.openings_append_singleton (events.take k.val) event] at actual
    exact actual
  have suffixes (k : Fin events.length) :
      ((B.openingPrefix events k.val).suffix (events.get k).hinge).Outward :=
    (control (events.take k.val) (openingBudget_take_le events k.val)).2 (events.get k).hinge
  have base_ne : B.direction ≠ 0 := R.openings_direction_ne_zero saved nonzero
  let Q := B.openingPrefix events events.length
  have last_ne : Q.direction ≠ 0 := B.openingPrefix_direction_ne_zero events _ base_ne
  have speed (k : Fin events.length)
      (r : Set.Ioi (nndist (B.openingPrefix events k.val).start
        ((B.openingPrefix events k.val).chain.vertex (events.get k).hinge))) :
      (B.openingPrefix events k.val).hingeCircleLift (events.get k).hinge
        (B.openingPrefix_direction_ne_zero events k.val base_ne) (events.get k).angle
        (fun θ hθ => sweeps k ⟨θ, hθ⟩) (positive k) r
        ⟨(events.get k).angle, (positive k).le, le_rfl⟩ ≤ (2 / m) * (events.get k).angle := by
    let P := B.openingPrefix events k.val
    let wordAt (θ : ℝ) := events.take k.val ++ [⟨(events.get k).hinge, θ⟩]
    have moved (θ : ℝ) :
        P.rotateSuffix (events.get k).hinge θ = R.openings (saved ++ wordAt θ) := by
      rw [R.openings_append]
      exact (B.openings_append_singleton (events.take k.val)
        ⟨(events.get k).hinge, θ⟩).symm
    have partial_budget (θ : ℝ) (hθ : θ ∈ Set.Icc 0 (events.get k).angle) :
        openingBudget (saved ++ wordAt θ) ≤ ε :=
      budget _ (openingBudget_take_partial_le events k θ hθ)
    refine P.hingeCircleLift_last_le_of_vertex_margin (events.get k).hinge
      (B.openingPrefix_direction_ne_zero events k.val base_ne) (events.get k).angle
      (fun θ hθ => sweeps k ⟨θ, hθ⟩) (positive k) (suffixes k) (small k) r m_pos m_le_one ?_ ?_ ?_
    · intro i
      change ((R.openings saved).openings (events.take k.val)).chain.edge i ≠ 0
      rw [← R.openings_append, R.openings_chain, R.chain.openings_edge]
      exact mul_ne_zero (polarRay_ne_zero _) (edges_ne i)
    · intro θ hθ i _
      dsimp only
      rw [moved θ]
      have bound := R.chain.radial_margin_of_heading_oscillation
        (R.chain.openings (saved ++ wordAt θ)) (openingHeading (saved ++ wordAt θ))
        (R.chain.openings_edge (saved ++ wordAt θ)) epsilon constant radial_budget
        (fun i j => (openingHeading_oscillation (saved ++ wordAt θ) i j).trans
          (partial_budget θ hθ)) length_bound margin 0 i (Nat.zero_le _)
      rw [← R.openings_chain] at bound
      exact bound
    · intro θ hθ
      dsimp only
      rw [moved θ]
      exact R.openings_tail_radial_margin (saved ++ wordAt θ) constant tail_length tail_margin
        (partial_budget θ hθ) radial_budget 0
  have phase (r : ℝ≥0) (hr : 0 < r) :
      0 < (B.twoBankRatio Q (states 0) base_ne (states events.length) last_ne r).im :=
    B.openingTrace_final_positive_phase_of_speed events base_ne states sweeps suffixes positive
      small (by positivity) angle_budget speed first source_hinge r hr
  have common : Q.start = B.start := B.openingPrefix_start events _
  simpa only [Q, B, openingPrefix, List.take_length, ← R.openings_append, R.openings_start] using
    B.exists_twoBankGap_of_positive_phase Q (states 0) base_ne (states events.length)
      last_ne common phase

end Unfoldings.PolygonalRay
