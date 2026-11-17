module

public import Unfoldings.Cone.TransportedCharts
public import Unfoldings.Metric.CenteredBallChartRestriction

/-! Original tangent fans inherit physically placed whole local metric-model charts. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (retain : Set C.Seam) (vertex : C.Vertex retain)
  {Y : Type*} [MetricSpace Y] (place : Y → Space) {a : Y} {ρ : ℝ}

/-- Transport an actual centered local model to the original retained corner fan, keeping
every original tagged tangent-cell coordinate and its literal spatial placement. -/
theorem exists_placed_tangentChart (positive : 0 < ρ)
    (B : Metric.eball (C.vertexPoint retain vertex) (ENNReal.ofReal ρ) ≃ᵢ Metric.ball a ρ)
    (center : (B ⟨C.vertexPoint retain vertex,
      Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩).val = a)
    (agrees : ∀ z, place (B z).val = F.toSpace retain z.val) :
    ∃ r : ℝ, 0 < r ∧
      ∃ D : Metric.eball (C.tangentOrigin retain vertex) (ENNReal.ofReal r) ≃ᵢ Metric.ball a r,
        ∀ (b : C.TangentTotal retain vertex)
          (near : edist (C.tangentPoint retain vertex b) (C.tangentOrigin retain vertex) <
            ENNReal.ofReal r),
          place (D ⟨C.tangentPoint retain vertex b, near⟩).val =
            F.toSpace retain (C.tangentSurfaceTag retain vertex b) := by
  let N := F.tangentChart retain vertex
  have center_N := N.chart_origin (Metric.mem_eball_self (ENNReal.ofReal_pos.mpr N.positive))
  let radius := min N.radius ρ
  let first := restrictCenteredEBallEquiv (ENNReal.ofReal_pos.mpr N.positive)
    (ENNReal.ofReal_le_ofReal (min_le_left N.radius ρ)) N.chart center_N
  let last := restrictCenteredBallChart positive (min_le_right N.radius ρ) B center
  refine ⟨radius, lt_min N.positive positive, first.trans last, ?_⟩
  intro b near
  let z : Metric.eball (C.tangentOrigin retain vertex) (ENNReal.ofReal radius) :=
    ⟨C.tangentPoint retain vertex b, near⟩
  have first_agrees : (first z).val = C.tangentSurfaceTag retain vertex b :=
    (restrictCenteredEBallEquiv_val (ENNReal.ofReal_pos.mpr N.positive)
      (ENNReal.ofReal_le_ofReal (min_le_left N.radius ρ)) N.chart center_N z).trans
      (N.agrees b (near.trans_le (ENNReal.ofReal_le_ofReal (min_le_left N.radius ρ))))
  have coordinates := restrictCenteredBallChart_val positive (min_le_right N.radius ρ)
    B center (first z)
  exact (congrArg place coordinates).trans
    ((agrees _).trans (congrArg (F.toSpace retain) first_agrees))

end Unfoldings.SpatialFolding
