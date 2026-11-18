module

public import Unfoldings.Metric.Local
public import Unfoldings.Metric.BallChart

/-! Actual cell interiors have whole Euclidean metric balls in every boundary-only gluing. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {I E : Type*} [MetricSpace E] (cells : I → Set E)
  (glue : Total (fun i => cells i) → Total (fun i => cells i) → Prop)

/-- Boundary-only attachment derives local Euclidean regularity on every actual cell interior.
No finiteness, global separation, convexity or developed placement hypothesis is needed. -/
theorem hasMetricBallChart_of_cell_interior
    (boundary : ∀ i p, p ∈ seamSupport (fun i => cells i) glue i →
      p.val ∉ interior (cells i))
    (i : I) (p : cells i) (inside : p.val ∈ interior (cells i)) :
    HasMetricBallChart E (of (fun i => cells i) glue i p) := by
  obtain ⟨ε, positive, contained⟩ := Metric.isOpen_iff.mp isOpen_interior p.val inside
  let r := ε / 4
  have rpos : 0 < r := div_pos positive (by norm_num)
  have clearance : ∀ z ∈ seamSupport (fun i => cells i) glue i, 3 * r ≤ dist z p := by
    intro z seam
    by_contra near
    apply boundary i z seam
    apply contained
    change dist z.val p.val < ε
    have bound : dist z p < 3 * r := lt_of_not_ge near
    change dist z.val p.val < 3 * r at bound
    dsimp [r] at bound
    linarith
  have in_cell (y : Metric.ball p.val r) : y.val ∈ cells i := by
    apply interior_subset (contained ?_)
    have close := y.property
    change dist y.val p.val < r at close
    change dist y.val p.val < ε
    dsimp [r] at close
    linarith
  let ambient : Metric.ball p r ≃ᵢ Metric.ball p.val r := {
    toFun := fun q => ⟨q.val.val, q.property⟩
    invFun := fun q => ⟨⟨q.val, in_cell q⟩, q.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    isometry_toFun := fun _ _ => rfl }
  exact ⟨r, rpos, p.val, ⟨(ballIsometry (fun i => cells i) glue i p rpos.le
    clearance).symm.trans ambient⟩⟩

end Unfoldings.MetricGluing
