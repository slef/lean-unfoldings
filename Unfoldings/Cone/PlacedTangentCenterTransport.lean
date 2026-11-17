module

public import Unfoldings.Cone.PlacedTangentCharts
public import Unfoldings.Metric.BallIsometry

/-! A placed model at the same actual vertex copy models its full tagged tangent fan. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

/-- Preserve the original physical model and its center when a named point is an actual
cut vertex. The whole tangent fan, with all original cell tags, is constructed. -/
theorem exists_placed_tangentChart_of_point_eq (retain : Set C.Seam) (vertex : C.Vertex retain)
    {Z : Type*} [MetricSpace Z] (place : Z → Space) {y : C.Realization retain}
    (same : C.vertexPoint retain vertex = y) {a : Z} {radius : ℝ} (positive : 0 < radius)
    (H : Metric.eball y (ENNReal.ofReal radius) ≃ᵢ Metric.ball a radius)
    (center_H : (H ⟨y, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩).val = a)
    (agrees_H : ∀ z, place (H z).val = F.toSpace retain z.val) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ D : Metric.eball (C.tangentOrigin retain vertex) (ENNReal.ofReal ε) ≃ᵢ Metric.ball a ε,
        ∀ (b : C.TangentTotal retain vertex)
          (near : edist (C.tangentPoint retain vertex b) (C.tangentOrigin retain vertex) <
            ENNReal.ofReal ε),
          place (D ⟨C.tangentPoint retain vertex b, near⟩).val =
            F.toSpace retain (C.tangentSurfaceTag retain vertex b) := by
  let x := C.vertexPoint retain vertex
  let move := basedEBallIsometry (IsometryEquiv.refl _) x y same (ENNReal.ofReal radius)
  let chart := move.trans H
  have center : (chart ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩).val = a := by
    have moved : move ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩ =
        ⟨y, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩ := Subtype.ext same
    change (H (move _)).val = a
    rw [moved]
    exact center_H
  exact F.exists_placed_tangentChart retain vertex place positive chart center
    (fun z => agrees_H (move z))

end Unfoldings.SpatialFolding
