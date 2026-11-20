module

public import Unfoldings.Convex.ActiveRayProgress
public import Unfoldings.Geometry.PolygonalLength
public import Unfoldings.Geometry.RadialNormProgress

/-! The monotonicity invariant induced by an interior progress body. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope

open InnerProductGeometry

/-- Directions whose value under the active slope dominates the whole progress body. -/
def historyCone (L : Set Plane) (p : Plane) : Set Plane :=
  {d | ∀ w ∈ L, inner ℝ w d ≤ inner ℝ p d}

/-- The invariant on two chronological points of a path driven by the envelope. -/
def HistoryProgress (E : SlopeEnvelope) (L : Set Plane) (x y : Plane) : Prop :=
  ∀ w ∈ L, inner ℝ w (y - x) ≤ E.height y - E.height x

variable (E : SlopeEnvelope) {L : Set Plane}

theorem HistoryProgress.refl (x : Plane) : E.HistoryProgress L x x := by
  intro w _
  simp

theorem HistoryProgress.trans {x y z : Plane}
    (first : E.HistoryProgress L x y) (last : E.HistoryProgress L y z) :
    E.HistoryProgress L x z := by
  intro w hw
  have split : z - x = (y - x) + (z - y) := by abel
  rw [split, inner_add_right]
  linarith [first w hw, last w hw]

/-- An active slope at a merger controls every displacement for which the
progress-body invariant holds, irrespective of the histories reaching it. -/
theorem HistoryProgress.mem_historyCone {x y p : Plane}
    (progress : E.HistoryProgress L x y) (active : E.Active y p) :
    y - x ∈ historyCone L p :=
  fun w hw => (progress w hw).trans (E.active_support active x)

/-- The initial directional commitment gives progress on every partial edge,
even when the active slope changes along that edge. -/
theorem historyProgress_ray {x p d : Plane} (active : E.Active x p)
    (direction : d ∈ historyCone L p) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    E.HistoryProgress L (x + s • d) (x + t • d) := by
  obtain ⟨q, active_q, dominates⟩ := E.exists_active_along_ray active hs
  intro w hw
  have progress := E.active_support active_q (x + t • d)
  have forward : (x + t • d) - (x + s • d) = (t - s) • d := by module
  have backward : (x + s • d) - (x + t • d) = (s - t) • d := by module
  rw [backward, real_inner_smul_right] at progress
  rw [forward, real_inner_smul_right]
  have bound := mul_le_mul_of_nonneg_left ((direction w hw).trans dominates) (sub_nonneg.mpr hst)
  linarith

/-- A disk inside the progress body turns the history invariant into a
quantitative lower bound for the potential increment. -/
theorem HistoryProgress.norm_le {x y : Plane} (progress : E.HistoryProgress L x y)
    {r : ℝ} (positive : 0 < r) (disk : Metric.closedBall (0 : Plane) r ⊆ L) :
    r * ‖y - x‖ ≤ E.height y - E.height x := by
  by_cases same : y = x
  · simp [same]
  let d := y - x
  have nonzero : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr same)
  let w := (r / ‖d‖) • d
  have member : w ∈ L := by
    apply disk
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ nonzero]
  have support := progress w member
  change inner ℝ ((r / ‖d‖) • d) d ≤ _ at support
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at support
  have scale : r / ‖d‖ * ‖d‖ ^ 2 = r * ‖d‖ := by
    field_simp
  rwa [scale] at support

/-- The length bound applies to any finite path made of admissible partial links. -/
theorem historyProgress_chain_length {r b : ℝ} (positive : 0 < r)
    (disk : Metric.closedBall (0 : Plane) r ⊆ L) (upper : ∀ p ∈ E.slopes, ‖p‖ ≤ b)
    {n : ℕ} (path : PolygonalChain Plane n)
    (step : ∀ i : Fin n, E.HistoryProgress L (path.vertex i.castSucc) (path.vertex i.succ)) :
    path.projectedLength ≤ (b / r) * ‖path.vertex (Fin.last n) - path.vertex 0‖ :=
  E.history_length_bound positive upper
    (path.potential_progress E.height (fun i => (step i).norm_le E positive disk))

/-- If a represented cone has a known bisector and aperture, any sufficiently
close heading belongs to the cone and has a uniform inner-product margin with
all incoming directions. -/
theorem historyCone_heading {p axis d : Plane} {w θ : ℝ} (d_ne : d ≠ 0)
    (nonneg : 0 ≤ θ) (width : θ ≤ w) (acute : (w + θ) / 2 < Real.pi / 2)
    (cone : ∀ z : Plane, z ≠ 0 →
      (z ∈ historyCone L p ↔ angle axis z ≤ w / 2))
    (close : angle axis d ≤ θ / 2) :
    d ∈ historyCone L p ∧ ∀ z ∈ historyCone L p,
      Real.cos ((w + θ) / 2) * (‖z‖ * ‖d‖) ≤ inner ℝ z d := by
  refine ⟨(cone d d_ne).mpr (close.trans (by linarith)), ?_⟩
  intro z hz
  by_cases zero : z = 0
  · simp [zero]
  have angle_z := (cone z zero).mp hz
  have bound := angle_le_angle_add_angle z axis d
  rw [angle_comm z axis] at bound
  exact (angle_le_iff_cos_mul_norm_le zero d_ne (by linarith) (by linarith [Real.pi_pos])).mp
    (by linarith)

end Unfoldings.SlopeEnvelope
