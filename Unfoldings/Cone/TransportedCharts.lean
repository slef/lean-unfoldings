module

public import Unfoldings.Cone.VertexAvoidance
public import Unfoldings.Metric.CenteredBallRestriction

/-! Whole-ball inclusions preserve the original tangent fan and all face coordinates. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  (retain : Set C.Seam) (vertex : C.Vertex retain) {Y : Type*} [EMetricSpace Y]

include F in
/-- A whole chart at a specified original vertex carries its actual retained tangent fan
into the target, including every original tagged wedge coordinate. -/
theorem exists_tangentChart_of_localMap (f : C.Realization retain → Y)
    (local_chart : ∃ r : ℝ, 0 < r ∧
      ∃ B : Metric.eball (C.vertexPoint retain vertex) (ENNReal.ofReal r) ≃ᵢ
        Metric.eball (f (C.vertexPoint retain vertex)) (ENNReal.ofReal r),
        ∀ z, (B z).val = f z.val) :
    ∃ r : ℝ, 0 < r ∧
      ∃ D : Metric.eball (C.tangentOrigin retain vertex) (ENNReal.ofReal r) ≃ᵢ
        Metric.eball (f (C.vertexPoint retain vertex)) (ENNReal.ofReal r),
        ∀ (a : C.TangentTotal retain vertex)
          (near : edist (C.tangentPoint retain vertex a) (C.tangentOrigin retain vertex) <
            ENNReal.ofReal r),
          (D ⟨C.tangentPoint retain vertex a, near⟩).val =
            f (C.tangentSurfaceTag retain vertex a) := by
  obtain ⟨ρ, ρpos, B, agrees⟩ := local_chart
  let N := F.tangentChart retain vertex
  have center_N := N.chart_origin
    (Metric.mem_eball_self (ENNReal.ofReal_pos.mpr N.positive))
  have center_B : (B ⟨C.vertexPoint retain vertex,
      Metric.mem_eball_self (ENNReal.ofReal_pos.mpr ρpos)⟩).val =
      f (C.vertexPoint retain vertex) := agrees _
  let radius := min N.radius ρ
  let first := restrictCenteredEBallEquiv (ENNReal.ofReal_pos.mpr N.positive)
    (ENNReal.ofReal_le_ofReal (min_le_left N.radius ρ)) N.chart center_N
  let last := restrictCenteredEBallEquiv (ENNReal.ofReal_pos.mpr ρpos)
    (ENNReal.ofReal_le_ofReal (min_le_right N.radius ρ)) B center_B
  refine ⟨radius, lt_min N.positive ρpos, first.trans last, ?_⟩
  intro a near
  let z : Metric.eball (C.tangentOrigin retain vertex) (ENNReal.ofReal radius) :=
    ⟨C.tangentPoint retain vertex a, near⟩
  have first_agrees : (first z).val = C.tangentSurfaceTag retain vertex a :=
    (restrictCenteredEBallEquiv_val (ENNReal.ofReal_pos.mpr N.positive)
      (ENNReal.ofReal_le_ofReal (min_le_left N.radius ρ)) N.chart center_N z).trans
      (N.agrees a (near.trans_le (ENNReal.ofReal_le_ofReal (min_le_left N.radius ρ))))
  have last_agrees : (last (first z)).val = f (first z).val :=
    (restrictCenteredEBallEquiv_val (ENNReal.ofReal_pos.mpr ρpos)
      (ENNReal.ofReal_le_ofReal (min_le_right N.radius ρ)) B center_B (first z)).trans
      (agrees _)
  exact last_agrees.trans (congrArg f first_agrees)

end Unfoldings.SpatialFolding
