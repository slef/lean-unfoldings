module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! Uniform angle continuity on a compact annulus, independently of any mesh. -/

@[expose] public section

namespace Unfoldings

open InnerProductGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- One modulus controls all pairs of directions whose lengths lie between one half and one. -/
theorem exists_uniform_angle_delta {ε : ℝ} (positive : 0 < ε) :
    ∃ δ > 0, ∀ a b c d : E,
      1 / 2 ≤ ‖a‖ → ‖a‖ ≤ 1 → 1 / 2 ≤ ‖b‖ → ‖b‖ ≤ 1 →
      1 / 2 ≤ ‖c‖ → ‖c‖ ≤ 1 → 1 / 2 ≤ ‖d‖ → ‖d‖ ≤ 1 →
      dist a c < δ → dist b d < δ → |angle a b - angle c d| < ε := by
  let A : Set E := Metric.closedBall 0 1 ∩ {x | 1 / 2 ≤ ‖x‖}
  have compact : IsCompact A := (isCompact_closedBall (0 : E) 1).inter_right
    (isClosed_le continuous_const continuous_norm)
  have continuous : ContinuousOn (fun p : E × E => angle p.1 p.2) (A ×ˢ A) := by
    intro p hp
    apply (continuousAt_angle ?_ ?_).continuousWithinAt
    · intro equal
      have bound := hp.1.2
      norm_num [equal] at bound
    · intro equal
      have bound := hp.2.2
      norm_num [equal] at bound
  obtain ⟨δ, δpos, bound⟩ := Metric.uniformContinuousOn_iff.mp
    ((compact.prod compact).uniformContinuousOn_of_continuous continuous) ε positive
  refine ⟨δ, δpos, fun a b c d al au bl bu cl cu dl du first last => ?_⟩
  have memA (x : E) (lower : 1 / 2 ≤ ‖x‖) (upper : ‖x‖ ≤ 1) : x ∈ A :=
    ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using upper, lower⟩
  have result := bound (a, b) ⟨memA a al au, memA b bl bu⟩
    (c, d) ⟨memA c cl cu, memA d dl du⟩ (by simpa only [Prod.dist_eq, max_lt_iff] using
      (And.intro first last))
  rw [Real.dist_eq] at result
  exact result

end Unfoldings
