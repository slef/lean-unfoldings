module

public import Unfoldings.FewestNets.CheckedCyclicBody
public import Unfoldings.FewestNets.CheckedProgressBody
public import Unfoldings.FewestNets.CheckedRoutingSide
public import Unfoldings.FewestNets.CertifiedRoutingScalars

/-! Kernel-checkable geometric routing records independent of mesh family. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry Real

/-- The exact normalized rational progress body and its side witnesses. -/
structure RoutingCellWitness (S V : ℕ) where
  body : Fin V → ℚ × ℚ
  inradius : ℚ
  sides : Fin S → RoutingSideWitness V

namespace RoutingCellWitness

variable {S V : ℕ} (w : RoutingCellWitness S V)

def vertex (i : Fin V) : Plane := rationalPolygonPoint (w.body i)

def checkedVertex (D : ℕ) (i : Fin V) : CheckedPlane D (w.vertex i) :=
  CheckedPlane.rat D (w.body i).1 (w.body i).2

def progressBody : Set Plane := convexHull ℝ (Set.range w.vertex)

variable {D n m : ℕ} (hD : 0 < D) {w : RoutingCellWitness (n + 1) (m + 1)}
  {corner normal : Fin (n + 1) → Plane} {offset : Fin (n + 1) → ℝ}
  (cp : ∀ k, CheckedPlane D (corner k)) (cn : ∀ k, CheckedPlane D (normal k))
  (co : ∀ k, CheckedReal D (offset k)) (scalar : DevelopmentScalarRecord)

def checkBody (w : RoutingCellWitness (n + 1) (m + 1)) : Bool :=
  decide (0 < w.inradius) &&
    decide (∀ i j, w.body i = w.body j → i = j) &&
    checkCyclicRationalBody w.body (finRotate (m + 1)) &&
    checkProgressBodyInradius hD (w.checkedVertex D) (CheckedReal.rat D w.inradius)

def checkCellSize (w : RoutingCellWitness (n + 1) (m + 1)) : Bool :=
  let limit := (CheckedReal.rat D scalar.lengthConstant).mul hD (CheckedReal.rat D w.inradius)
  (List.finRange (n + 1)).all fun k => (CheckedPlane.norm hD (cp k)).isLT limit

def checkAllSides (w : RoutingCellWitness (n + 1) (m + 1)) : Bool :=
  (List.finRange (n + 1)).all fun k =>
    checkRoutingSide hD (cp (k - 1)) (cp k) (cn k) (w.checkedVertex D) (finRotate (m + 1))
      (co k) (CheckedReal.rat D scalar.cotangent) (CheckedReal.rat D scalar.margin) (w.sides k)

/-- Validate the shape, disk, radius-to-inradius ratio and all side data. -/
def check (w : RoutingCellWitness (n + 1) (m + 1)) : Bool :=
  checkBody hD w && checkCellSize hD cp scalar w && checkAllSides hD cp cn co scalar w

theorem body_of_check (passed : checkBody hD w = true) :
    (0 : ℝ) < w.inradius ∧ Function.Injective w.vertex ∧
      CyclicConvexVertices w.vertex (finRotate (m + 1)) ∧
      Metric.closedBall (0 : Plane) (w.inradius : ℝ) ⊆ w.progressBody := by
  simp only [checkBody, Bool.and_eq_true, decide_eq_true_eq] at passed
  have positive : (0 : ℝ) < w.inradius := by exact_mod_cast passed.1.1.1
  refine ⟨positive, rationalPolygonPoint_injective.comp passed.1.1.2,
    cyclicConvex_of_check w.body _ passed.1.2, ?_⟩
  exact closedBall_subset_progressBody_of_check hD (w.checkedVertex D)
    (CheckedReal.rat D w.inradius) positive.le passed.2

theorem radius_bound_of_check (passed : checkCellSize hD cp scalar w = true) :
    ∀ x ∈ convexHull ℝ (Set.range corner), ‖x‖ < (scalar.lengthConstant : ℝ) * w.inradius := by
  have ball : convexHull ℝ (Set.range corner) ⊆
      Metric.ball 0 ((scalar.lengthConstant : ℝ) * w.inradius) := by
    apply convexHull_min _ (convex_ball _ _)
    rintro _ ⟨i, rfl⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact CheckedReal.lt_of_isLT hD _ _ (List.all_eq_true.mp passed i (List.mem_finRange i))
  intro x member
  exact (mem_ball_zero_iff.mp (ball member))

/-- The inradius and radius ratio, with strict side and cone estimates in
the exact normalized coordinates of this record. -/
theorem geometry_of_check {target : ℚ} (nonnegative : 0 ≤ target)
    (valid : scalar.ValidFor target) (cot_gap : 0 < scalar.cotangentGap)
    (passed : check hD cp cn co scalar w = true)
    (unit : ∀ k, ‖normal k‖ = 1) :
    (0 : ℝ) < w.inradius ∧
    Metric.closedBall (0 : Plane) (w.inradius : ℝ) ⊆ w.progressBody ∧
    (∀ x ∈ convexHull ℝ (Set.range corner), ‖x‖ < (scalar.lengthConstant : ℝ) * w.inradius) ∧
    ∀ k, w.progressBody ⊆ {y | inner ℝ (normal k) y < offset k} ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        let p := AffineMap.lineMap (corner (k - 1)) (corner k) t
        offset k ≤ inner ℝ (normal k) p →
        (∃ axis : Plane, ∃ width : ℝ, axis ≠ 0 ∧
          scalar.visualAngle < width ∧ width < π - scalar.visualAngle ∧
          ∀ z : Plane, z ≠ 0 →
            (z ∈ SlopeEnvelope.historyCone w.progressBody p ↔ angle axis z ≤ width / 2)) ∧
        ∀ z : Plane, z ∈ SlopeEnvelope.historyCone w.progressBody p →
          (scalar.margin : ℝ) * ‖z‖ ≤ inner ℝ (normal k) z := by
  simp only [check, Bool.and_eq_true] at passed
  obtain ⟨rpos, distinct, convex, disk⟩ := body_of_check hD passed.1.1
  refine ⟨rpos, disk, radius_bound_of_check hD cp scalar passed.1.2, ?_⟩
  intro k
  let cw := w.checkedVertex D
  let ct := CheckedReal.rat D scalar.cotangent
  let cg := CheckedReal.rat D scalar.margin
  have test := List.all_eq_true.mp passed.2 k (List.mem_finRange k)
  constructor
  · have side := test
    simp only [checkRoutingSide, Bool.and_eq_true] at side
    exact progressBody_strictSide_of_check hD (cn k) cw (co k) side.1.1.1.1.1.1
  · intro t ht
    have cot_nonnegative : (0 : ℝ) ≤ scalar.cotangent := by
      exact_mod_cast valid.2.2.2.2.1.le
    exact routingCone_of_check hD (cp (k - 1)) (cp k) (cn k) cw convex distinct
      (co k) ct cg (scalar.visualAngle_pos nonnegative valid)
      (scalar.visualAngle_lt_pi_div_two valid).le cot_nonnegative
      (scalar.cotangent_lt_of_gap cot_gap) (scalar.margin_nonneg valid) (unit k)
      (w.sides k) test ht

end RoutingCellWitness
end Unfoldings.FewestNets
