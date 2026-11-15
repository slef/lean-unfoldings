module

public import Unfoldings.Geometry.TwoBankGapCells
public import Unfoldings.Metric.PolygonalClosedCover
public import Unfoldings.Metric.Connected
public import Mathlib.Analysis.Convex.Contractible

/-! Complete intrinsic metrics and exact sector topology for actual two-bank Jordan gaps. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ n) (Q : PolygonalRay ℂ m)
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)
  (common : Q.start = R.start)

include common in
theorem twoBankGap_complete :
    CompleteSpace (PolygonalPoint
      (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase)) := by
  obtain ⟨I, inst, cells, properties, _, cover⟩ :=
    R.exists_twoBankGap_cell_cover Q first_outward first_nonzero last_outward last_nonzero
      positive_phase common
  let : Fintype I := inst
  exact PolygonalPoint.completeSpace_of_finite_closed_cover cells
    (fun i => (properties i).1) (fun i => (properties i).2.1) cover

include common in
theorem twoBankGap_continuous_ofSubtype :
    Continuous (PolygonalPoint.ofSubtype (s :=
      R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase)) := by
  obtain ⟨I, inst, cells, properties, _, cover⟩ :=
    R.exists_twoBankGap_cell_cover Q first_outward first_nonzero last_outward last_nonzero
      positive_phase common
  let : Fintype I := inst
  exact PolygonalPoint.continuous_ofSubtype_of_finite_closed_cover cells
    (fun i => (properties i).1) (fun i => (properties i).2.1) cover

/-- The intrinsic and ambient topologies agree, including every actual bank point. -/
def twoBankGapIntrinsicHomeomorph :
    PolygonalPoint
      (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase) ≃ₜ
        R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase where
  toFun := PolygonalPoint.toSubtype
  invFun := PolygonalPoint.ofSubtype
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := PolygonalPoint.continuous_toSubtype
  continuous_invFun := R.twoBankGap_continuous_ofSubtype Q first_outward first_nonzero
    last_outward last_nonzero positive_phase common

/-- The actual intrinsic gap is homeomorphic to one closed convex right-angle sector. -/
def twoBankGapSectorHomeomorph :
    PolygonalPoint
      (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase) ≃ₜ
        planarSector (Real.pi / 2) :=
  (R.twoBankGapIntrinsicHomeomorph Q first_outward first_nonzero last_outward last_nonzero
    positive_phase common).trans
    ((R.twoBankFrame Q first_outward first_nonzero last_outward last_nonzero positive_phase).image
      (planarSector (Real.pi / 2))).symm

include common in
theorem twoBankGap_contractible :
    ContractibleSpace (PolygonalPoint
      (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase)) := by
  let : ContractibleSpace (planarSector (Real.pi / 2)) :=
    (convex_planarSector (Real.pi / 2)).contractibleSpace
      ⟨0, 0, le_rfl, 0, le_rfl, by simp⟩
  exact (R.twoBankGapSectorHomeomorph Q first_outward first_nonzero last_outward last_nonzero
    positive_phase common).contractibleSpace

include common in
theorem twoBankGap_edist_ne_top
    (x y : PolygonalPoint
      (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase)) :
    edist x y ≠ ⊤ := by
  let : ContractibleSpace (PolygonalPoint
      (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase)) :=
    R.twoBankGap_contractible Q first_outward first_nonzero last_outward last_nonzero
      positive_phase common
  exact edist_ne_top_of_preconnected x y

/-- This genuine metric uses the proved finite intrinsic polygonal distances. -/
@[instance_reducible] def twoBankGapMetricSpace :
    MetricSpace (PolygonalPoint
      (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase)) :=
  EMetricSpace.toMetricSpace (R.twoBankGap_edist_ne_top Q first_outward first_nonzero
    last_outward last_nonzero positive_phase common)

/-- Every actual interior point has a metric-ball Euclidean chart. -/
theorem twoBankGap_interior_chart
    (x : PolygonalPoint
      (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase))
    (inside : x.val ∈ interior
      (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase)) :
    HasMetricBallChart ℂ x := by
  obtain ⟨r, positive, included⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp inside)
  exact PolygonalPoint.hasMetricBallChart_of_ball positive included

end Unfoldings.PolygonalRay
