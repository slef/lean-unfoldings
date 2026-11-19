module

public import Unfoldings.Metric.InternalFamilyBalls

/-! Internal piece-ball identifications retain their named original centers. -/

@[expose] public section

namespace Unfoldings.MetricGluing

variable {I : Type*} {J : I → Type*} (E : ∀ i, J i → Type*) [Finite I]
  [∀ i j, MetricSpace (E i j)] (S : ∀ i, ClosedSeams (E i))

/-- The whole-ball identification sends the original piece center to its original raw-cell copy. -/
theorem internalFamilyCellBall_center (i : I) (j : J i) (p : E i j) {r : ℝ} (positive : 0 < r) :
    (internalFamilyCellBall E S i j p r
      ⟨of (E i) (S i).relation j p,
        Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩).val =
      of (NestedCell E) (ClosedSeams.ofFamily E S).relation ⟨i, j⟩ p := rfl

end Unfoldings.MetricGluing
