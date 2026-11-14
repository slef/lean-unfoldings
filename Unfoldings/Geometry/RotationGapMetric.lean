module

public import Unfoldings.Geometry.PolygonalGapCells
public import Unfoldings.Metric.PolygonalClosedCover
public import Unfoldings.Metric.Connected
public import Mathlib.Analysis.Convex.Contractible

/-! Construct complete intrinsic metrics and exact sector topology for polygonal rotation gaps. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (outward : R.Outward) (nonzero : R.direction ≠ 0)
  (angle : ℝ) (sine : Real.sin angle ≠ 0)

include sine in
/-- The actual gap's intrinsic metric is complete, including both banks and its infinite end. -/
theorem rotationGap_complete :
    CompleteSpace (PolygonalPoint (R.rotationGap outward nonzero angle)) := by
  obtain ⟨I, inst, cells, properties, _, cover⟩ :=
    R.exists_rotationGap_cell_cover outward nonzero angle sine
  let : Fintype I := inst
  exact PolygonalPoint.completeSpace_of_finite_closed_cover cells
    (fun i => (properties i).1) (fun i => (properties i).2.1) cover

include sine in
theorem rotationGap_continuous_ofSubtype :
    Continuous (PolygonalPoint.ofSubtype (s := R.rotationGap outward nonzero angle)) := by
  obtain ⟨I, inst, cells, properties, _, cover⟩ :=
    R.exists_rotationGap_cell_cover outward nonzero angle sine
  let : Fintype I := inst
  exact PolygonalPoint.continuous_ofSubtype_of_finite_closed_cover cells
    (fun i => (properties i).1) (fun i => (properties i).2.1) cover

/-- At boundary points too, the intrinsic and ambient topologies agree. -/
def rotationGapIntrinsicHomeomorph :
    PolygonalPoint (R.rotationGap outward nonzero angle) ≃ₜ
      R.rotationGap outward nonzero angle where
  toFun := PolygonalPoint.toSubtype
  invFun := PolygonalPoint.ofSubtype
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := PolygonalPoint.continuous_toSubtype
  continuous_invFun := R.rotationGap_continuous_ofSubtype outward nonzero angle sine

/-- A concrete homeomorphism from the intrinsic polygonal gap onto a closed sector. -/
def rotationGapSectorHomeomorph :
    PolygonalPoint (R.rotationGap outward nonzero angle) ≃ₜ planarSector angle :=
  (R.rotationGapIntrinsicHomeomorph outward nonzero angle sine).trans
    ((R.bankFrame outward nonzero).image (planarSector angle)).symm

include sine in
/-- No disk or simple-connectedness certificate is assumed for the constructed intrinsic gap. -/
theorem rotationGap_contractible :
    ContractibleSpace (PolygonalPoint (R.rotationGap outward nonzero angle)) := by
  have full : (planarSector angle).Nonempty := ⟨0, 0, le_rfl, 0, le_rfl, by simp⟩
  let : ContractibleSpace (planarSector angle) := (convex_planarSector angle).contractibleSpace full
  exact (R.rotationGapSectorHomeomorph outward nonzero angle sine).contractibleSpace

include sine in
/-- Connectedness makes every actual intrinsic polygonal distance finite. -/
theorem rotationGap_edist_ne_top
    (x y : PolygonalPoint (R.rotationGap outward nonzero angle)) : edist x y ≠ ⊤ := by
  let : ContractibleSpace (PolygonalPoint (R.rotationGap outward nonzero angle)) :=
    R.rotationGap_contractible outward nonzero angle sine
  exact edist_ne_top_of_preconnected x y

/-- The constructed gap has a genuine metric, with the proved intrinsic route distances. -/
@[instance_reducible] def rotationGapMetricSpace :
    MetricSpace (PolygonalPoint (R.rotationGap outward nonzero angle)) :=
  EMetricSpace.toMetricSpace (R.rotationGap_edist_ne_top outward nonzero angle sine)

/-- Every interior point has an actual metric-ball Euclidean chart. -/
theorem rotationGap_interior_chart (x : PolygonalPoint (R.rotationGap outward nonzero angle))
    (inside : x.val ∈ interior (R.rotationGap outward nonzero angle)) : HasMetricBallChart ℂ x := by
  obtain ⟨r, positive, included⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp inside)
  exact PolygonalPoint.hasMetricBallChart_of_ball positive included

end Unfoldings.PolygonalRay
