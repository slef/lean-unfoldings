module

public import Unfoldings.Cone.SectorPairBall
public import Unfoldings.Metric.CenteredBallRestriction

/-! Place and restrict two independently constructed, centered angular-sector charts. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing.SectorPairChart

variable {I : Type*} {X : I → Type*} [∀ i, EMetricSpace (X i)] (a : Bool → Total X)
  {θ κ : ℝ} (positive : 0 < θ) (small : θ < 2 * Real.pi)
  (gap_pos : 0 < κ) (balance : θ + κ = 2 * Real.pi)

local notation "U" => rotation (Circle.exp θ)

/-- Place a chart for the second component in the geometric complement of the first. -/
def complementaryPlacement :
    PolygonalPoint (closedAngularSector κ) ≃ᵢ PolygonalPoint (complementarySectorRegion θ true) :=
  PolygonalPoint.affineRegionIsometryEquiv (U).toAffineIsometryEquiv (by
    change (U) '' closedAngularSector (2 * Real.pi - θ) = _
    rw [show 2 * Real.pi - θ = κ by linarith only [balance]]
    rfl)

@[simp] theorem complementaryPlacement_val (x : PolygonalPoint (closedAngularSector κ)) :
    (complementaryPlacement balance x).val = (U) x.val := rfl

@[simp] theorem complementaryPlacement_center :
    complementaryPlacement balance (closedAngularSectorOrigin gap_pos.le) = (complementarySectorOrigin positive small true) :=
  PolygonalPoint.ext ((U).map_zero)

variable {r₀ r₁ r : ℝ}
  (first_pos : 0 < r₀) (second_pos : 0 < r₁) (radius_pos : 0 < r)
  (first_fit : r ≤ r₀) (second_fit : r ≤ r₁)
  (first : Metric.eball (a false).2 (ENNReal.ofReal r₀) ≃ᵢ
    Metric.eball (complementarySectorOrigin positive small false) (ENNReal.ofReal r₀))
  (second : Metric.eball (a true).2 (ENNReal.ofReal r₁) ≃ᵢ
    Metric.eball (closedAngularSectorOrigin gap_pos.le) (ENNReal.ofReal r₁))
  (first_center :
    (first ⟨(a false).2, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr first_pos)⟩).val =
      complementarySectorOrigin positive small false)
  (second_center :
    (second ⟨(a true).2, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr second_pos)⟩).val =
      closedAngularSectorOrigin gap_pos.le)
  (distinct : (a false).1 ≠ (a true).1)

/-- The selected common radius retains the whole first and second sector balls. -/
def fromSectors : SectorPairChart X a positive small r := by
  let firstChart := restrictCenteredEBallEquiv (ENNReal.ofReal_pos.mpr first_pos)
    (ENNReal.ofReal_le_ofReal first_fit) first first_center
  let secondChart := (restrictCenteredEBallEquiv (ENNReal.ofReal_pos.mpr second_pos)
      (ENNReal.ofReal_le_ofReal second_fit) second second_center).trans
    (basedEBallIsometry (complementaryPlacement balance)
      (closedAngularSectorOrigin gap_pos.le) ((complementarySectorOrigin positive small true))
      (complementaryPlacement_center positive small gap_pos balance) (ENNReal.ofReal r))
  let chart := @Bool.rec (fun b =>
    Metric.eball (a b).2 (ENNReal.ofReal r) ≃ᵢ Metric.eball ((complementarySectorOrigin positive small b)) (ENNReal.ofReal r))
    firstChart secondChart
  have centerFirst : (firstChart
      ⟨(a false).2, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr radius_pos)⟩).val =
      complementarySectorOrigin positive small false :=
    (restrictCenteredEBallEquiv_val _ _ first first_center _).trans first_center
  have centerSecond : (secondChart
      ⟨(a true).2, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr radius_pos)⟩).val =
      complementarySectorOrigin positive small true :=
    (congrArg (complementaryPlacement balance)
      ((restrictCenteredEBallEquiv_val _ _ second second_center _).trans second_center)).trans
        (complementaryPlacement_center positive small gap_pos balance)
  exact ⟨radius_pos, distinct, chart, @Bool.rec (fun b =>
    (chart b ⟨(a b).2, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr radius_pos)⟩).val =
      complementarySectorOrigin positive small b)
    centerFirst centerSecond⟩

end Unfoldings.MetricGluing.SectorPairChart
