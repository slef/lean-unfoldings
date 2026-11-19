module

public import Unfoldings.Complex.IntrinsicBoundary
public import Unfoldings.Geometry.EdgeHalfPlaneMetric

/-! Original nonvertex bank charts retain whole occupied half-plane metric balls and bank points. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex.BoundaryChart

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} {bank : C.BoundaryBank retain}
  {x : (C.triangle bank.val.face).Edge bank.val.edge} (N : C.BoundaryChart retain bank x)

/-- Express the constructed original boundary chart in its entire occupied half-plane metric. -/
def halfPlaneChart : Metric.eball (C.bankMap retain bank x) (ENNReal.ofReal N.radius) ≃ᵢ
    Metric.ball ((C.triangle bank.val.face).edgeHalfPlanePoint bank.val.edge x) N.radius :=
  N.chart.symm.trans ((C.triangle bank.val.face).edgeHalfPlaneBallIsometry bank.val.edge x N.radius)

/-- The half-plane chart retains the actual original edge center. -/
theorem halfPlaneChart_center :
    (N.halfPlaneChart ⟨C.bankMap retain bank x,
      Metric.mem_eball_self (ENNReal.ofReal_pos.mpr N.positive)⟩).val =
        (C.triangle bank.val.face).edgeHalfPlanePoint bank.val.edge x := by
  apply Subtype.ext
  exact N.center_coordinates

/-- Every nearby regular original bank point keeps its literal original face coordinates. -/
theorem halfPlaneChart_bankPoint (y : (C.triangle bank.val.face).Edge bank.val.edge)
    (regular : ¬ (C.triangle bank.val.face).IsVertex y)
    (near : C.bankMap retain bank y ∈ Metric.eball (C.bankMap retain bank x)
      (ENNReal.ofReal N.radius)) :
    (N.halfPlaneChart ⟨C.bankMap retain bank y, near⟩).val.val = y.val := by
  let target := (⟨C.bankMap retain bank y, near⟩ :
    Metric.eball (C.bankMap retain bank x) (ENNReal.ofReal N.radius))
  let p := N.chart.symm target
  have equal := (congrArg Subtype.val (N.chart.apply_symm_apply target)).symm.trans (N.agrees p)
  have tagged := (C.bankMap_eq_iff retain bank y regular _).mp equal
  exact (congrArg (fun a : C.Total => a.2.val) tagged).symm

end Unfoldings.TriangleComplex.BoundaryChart

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) {retain : Set C.Seam} {bank : C.BoundaryBank retain}
  {x : (C.triangle bank.val.face).Edge bank.val.edge} (N : C.BoundaryChart retain bank x)

/-- The whole original half-plane chart retains the exact original spatial face placement. -/
theorem boundary_halfPlaneChart_physical
    (z : Metric.eball (C.bankMap retain bank x) (ENNReal.ofReal N.radius)) :
    F.place bank.val.face (N.halfPlaneChart z).val.val = F.toSpace retain z.val := by
  have named := congrArg (F.toSpace retain) (N.agrees (N.chart.symm z))
  change F.toSpace retain (N.chart (N.chart.symm z)).val =
    F.place bank.val.face (N.halfPlaneChart z).val.val at named
  rw [N.chart.apply_symm_apply] at named
  exact named.symm

end Unfoldings.SpatialFolding
