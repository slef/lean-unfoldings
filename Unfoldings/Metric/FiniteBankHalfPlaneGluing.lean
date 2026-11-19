module

public import Unfoldings.Metric.BankHalfPlaneChart
public import Unfoldings.Metric.FiniteBankPairPlanarBall

/-! Closed finite banks with normalized original half-plane charts are locally planar. -/

@[expose] public section

open scoped ENNReal

namespace Unfoldings.MetricGluing

section Affine

variable {I A : Type*} (X : I → Type*) [∀ i, EMetricSpace (X i)] {i j : I}
  (left : A → X i) (right : A → X j) (t : A)

variable (param : A → ℝ)

/-- Whole closed banks with a common arclength parameter and matching centered charts
give a plane ball after gluing. Distinct nearby banks may be in one original piece. -/
theorem bankPair_planarBall_of_charts {R₁ R₂ speed : ℝ}
    (L : BankHalfPlaneChart left t false (fun s => (param s - param t) * speed) R₁)
    (D : BankHalfPlaneChart right t true (fun s => (param s - param t) * speed) R₂)
    (speed_pos : 0 < speed) (interior_time : param t ∈ interior (Set.range param))
    (left_metric : ∀ s, edist (left t) (left s) = ENNReal.ofReal (|param s - param t| * speed))
    (right_metric : ∀ s, edist (right t) (right s) =
      ENNReal.ofReal (|param s - param t| * speed))
    (left_closed : IsClosed (Set.range left)) (right_closed : IsClosed (Set.range right))
    (different_left : ∀ s, (⟨j, right t⟩ : Total X) ≠ ⟨i, left s⟩)
    (different_right : ∀ s, (⟨i, left t⟩ : Total X) ≠ ⟨j, right s⟩) :
    HasMetricBallChart ℂ (point X (bankPairGlue X left right) ⟨i, left t⟩) := by
  obtain ⟨δ, δpos, clear_left, clear_right⟩ :=
    exists_bankPair_clearance X left right t left_closed right_closed different_left different_right
  let d := (min δ 1).toReal
  have fin : min δ 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have dpos : 0 < d := ENNReal.toReal_pos (lt_min δpos zero_lt_one).ne' fin
  have dsmall : ENNReal.ofReal d ≤ δ := by
    change ENNReal.ofReal (min δ 1).toReal ≤ δ
    rw [ENNReal.ofReal_toReal fin]
    exact min_le_left _ _
  let R := min (min R₁ R₂) (d / 4)
  have positive : 0 < R := lt_min (lt_min L.positive D.positive) (div_pos dpos (by norm_num))
  have small_d : 4 * R ≤ d := by
    have bound : R ≤ d / 4 := min_le_right _ _
    linarith
  have small : ENNReal.ofReal R ≤ δ :=
    (ENNReal.ofReal_le_ofReal (by linarith)).trans dsmall
  have sep : ENNReal.ofReal (4 * R) ≤ faceCost X ⟨i, left t⟩ ⟨j, right t⟩ :=
    (ENNReal.ofReal_le_ofReal small_d).trans (dsmall.trans (clear_right t))
  let L' := L.restrict positive ((min_le_left _ _).trans (min_le_left _ _))
  let D' := D.restrict positive ((min_le_left _ _).trans (min_le_right _ _))
  let centers : Bool → Total X := fun side => Bool.rec ⟨i, left t⟩ ⟨j, right t⟩ side
  let C : BankPairChart X centers R :=
    { positive := positive
      separated := sep
      chart := fun side => match side with
        | false => L'.chart.trans (bankHalfPlaneBallIsometry false R)
        | true => D'.chart.trans (bankHalfPlaneBallIsometry true R)
      centered := by
        intro side
        cases side
        · exact congrArg Subtype.val L'.centered
        · exact congrArg Subtype.val D'.centered }
  apply bankPair_planarBall_of_affine_coordinates X left right t param C speed_pos interior_time
    left_metric right_metric
    (fun s => small.trans (clear_left s)) (fun s => small.trans (clear_right s))
  · intro s near
    exact (C.coordinates_near false _ near).trans (L'.parameter s _)
  · intro s near
    exact (C.coordinates_near true _ near).trans (D'.parameter s _)


end Affine

section Finite

variable {I : Type*} (X : I → Type*) [∀ i, EMetricSpace (X i)] {i j : I}
  (left : unitInterval → X i) (right : unitInterval → X j) (t : unitInterval)

/-- Whole closed banks with a common arclength parameter and matching centered charts
give a plane ball after gluing. Distinct nearby banks may be in one original piece. -/
theorem finiteBankPair_planarBall_of_charts {R₁ R₂ speed : ℝ}
    (L : BankHalfPlaneChart left t false (fun s => (s.val - t.val) * speed) R₁)
    (D : BankHalfPlaneChart right t true (fun s => (s.val - t.val) * speed) R₂)
    (speed_pos : 0 < speed) (bounds : 0 < t ∧ t < 1)
    (left_metric : ∀ s, edist (left t) (left s) = ENNReal.ofReal (|(s : ℝ) - t| * speed))
    (right_metric : ∀ s, edist (right t) (right s) =
      ENNReal.ofReal (|(s : ℝ) - t| * speed))
    (left_closed : IsClosed (Set.range left)) (right_closed : IsClosed (Set.range right))
    (different_left : ∀ s, (⟨j, right t⟩ : Total X) ≠ ⟨i, left s⟩)
    (different_right : ∀ s, (⟨i, left t⟩ : Total X) ≠ ⟨j, right s⟩) :
    HasMetricBallChart ℂ (point X (bankPairGlue X left right) ⟨i, left t⟩) := by
  apply bankPair_planarBall_of_charts X left right t Subtype.val L D speed_pos _
    left_metric right_metric left_closed right_closed different_left different_right
  rw [Subtype.range_coe]
  change t.val ∈ interior (Set.Icc (0 : ℝ) 1)
  rw [interior_Icc]
  exact bounds

end Finite
end Unfoldings.MetricGluing
