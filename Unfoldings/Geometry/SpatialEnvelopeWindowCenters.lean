module

public import Unfoldings.Geometry.SpatialEnvelopeWindowCut
public import Unfoldings.Metric.CenteredChartTransport

/-! Actual polygonal windows preserve whole neighborhoods at specified original patch copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A] {J : Type*}

/-- A strict-interior specified patch copy retains its whole neighborhood under inclusion. -/
theorem windowCut_ball_chart_at (equations : J → Plane →ᵃ[ℝ] ℝ) (signs : A → J → Bool)
    (aligned : ∀ a z, z ∈ P.footprint a → ∀ j,
      0 ≤ AffineArrangement.signed (equations j) (signs a j) z)
    (cuts : Set Plane) (source : P.WindowCut signs cuts)
    (positive : ∀ j, 0 < equations j
      (Cap.horizontal (P.restoreCut cuts (P.windowCutMap signs cuts source)).val)) :
    ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball source (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (P.windowCutMap signs cuts source) (ENNReal.ofReal r),
      ∀ z, (B z).val = P.windowCutMap signs cuts z.val := by
  obtain ⟨a, rfl⟩ := MetricGluing.point_surjective
    (fun a : {a // WindowSelected signs a} => P.spatialCell a.val)
    (MetricGluing.cutSeams (fun a : {a // WindowSelected signs a} => P.spatialCell a.val)
      (fun a => P.isClosed_spatialCell a.val) (Cap.horizontal ⁻¹' cuts)).relation source
  have physical := P.restoreCut_windowCutMap signs cuts
    (MetricGluing.point (fun a : {a // WindowSelected signs a} => P.spatialCell a.val)
      (MetricGluing.cutSeams (fun a : {a // WindowSelected signs a} => P.spatialCell a.val)
        (fun a => P.isClosed_spatialCell a.val) (Cap.horizontal ⁻¹' cuts)).relation a)
  have chosen : ∀ c, a.2.val ∈ P.spatialCell c → WindowSelected signs c := by
    intro c member
    apply P.windowSelected_of_spatial_mem equations signs aligned a.2.val _ c member
    intro j
    exact Eq.mp (congrArg (fun p : Space => 0 < equations j (Cap.horizontal p)) physical)
      (positive j)
  obtain ⟨r, rpos, B, agrees⟩ := MetricGluing.exists_cutSubfamily_ball_chart_of_cells_at_point
    P.spatialCell P.isClosed_spatialCell (Cap.horizontal ⁻¹' cuts) (WindowSelected signs) a chosen
  let root := MetricGluing.point (fun a => P.spatialCell a) (P.cutPhysicalSeams cuts).relation
    ⟨a.1.val, a.2⟩
  let move := basedEBallIsometry (P.cutIsometryEquiv cuts).symm root
    ((P.cutIsometryEquiv cuts).symm root) rfl (ENNReal.ofReal r)
  refine ⟨r, rpos, B.trans move, ?_⟩
  intro z
  exact congrArg (P.cutIsometryEquiv cuts).symm (agrees z)

end Unfoldings.SpatialEnvelope.WholePartition
