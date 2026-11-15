module

public import Unfoldings.Geometry.SpatialEnvelopeCut
public import Unfoldings.Metric.PolygonalCutGerm

/-! Exact whole-ball excision of distant roof cuts in the original rigid cell coordinates. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]

/-- Removing fewer horizontal cut points restores the actual retained rigid-cell seams. -/
theorem cutGlue_mono (cuts other : Set Plane) (included : other ⊆ cuts) :
    ∀ x y, P.cutGlue cuts x y → P.cutGlue other x y := by
  intro x y joined
  have original := ((P.cutPhysicalSeams cuts).offDiagonal_relation_iff
    ⟨x.1, P.cellIsometryEquiv x.1 x.2⟩ ⟨y.1, P.cellIsometryEquiv y.1 y.2⟩).mp joined
  apply ((P.cutPhysicalSeams other).offDiagonal_relation_iff
    ⟨x.1, P.cellIsometryEquiv x.1 x.2⟩ ⟨y.1, P.cellIsometryEquiv y.1 y.2⟩).mpr
  exact ⟨original.1, MetricGluing.cutSeams_relation_mono P.spatialCell P.isClosed_spatialCell
    (Cap.horizontal ⁻¹' cuts) (Set.preimage_mono included) _ _ original.2⟩

/-- Canonically restore selected cut pieces in this same actual whole-roof partition. -/
def forgetCut (cuts other : Set Plane) (included : other ⊆ cuts) : P.Cut cuts → P.Cut other :=
  MetricGluing.forget (fun a => P.planarCell a) (P.cutGlue_mono cuts other included)

@[simp] theorem forgetCut_of (cuts other : Set Plane) (included : other ⊆ cuts)
    (a : A) (x : P.planarCell a) :
    P.forgetCut cuts other included
      (MetricGluing.of (fun a => P.planarCell a) (P.cutGlue cuts) a x) =
      MetricGluing.of (fun a => P.planarCell a) (P.cutGlue other) a x := rfl

theorem forgetCut_lipschitz (cuts other : Set Plane) (included : other ⊆ cuts) :
    LipschitzWith 1 (P.forgetCut cuts other included) :=
  MetricGluing.forget_lipschitz (fun a => P.planarCell a) (P.cutGlue_mono cuts other included)

/-- Rigid coordinate changes commute with the actual physical restoration. -/
theorem cutIsometryEquiv_forgetCut (cuts other : Set Plane) (included : other ⊆ cuts)
    (x : P.Cut cuts) :
    P.cutIsometryEquiv other (P.forgetCut cuts other included x) =
      MetricGluing.forget (fun a => P.spatialCell a)
        (MetricGluing.cutSeams_relation_mono P.spatialCell P.isClosed_spatialCell
          (Cap.horizontal ⁻¹' cuts) (Set.preimage_mono included)) (P.cutIsometryEquiv cuts x) := by
  obtain ⟨a, rfl⟩ := MetricGluing.point_surjective (fun a => P.planarCell a) (P.cutGlue cuts) x
  rfl

/-- The actual physical graph point is unchanged when distant cuts are restored. -/
theorem restoreCut_forgetCut (cuts other : Set Plane) (included : other ⊆ cuts) (x : P.Cut cuts) :
    P.restoreCut other (P.forgetCut cuts other included x) = P.restoreCut cuts x := by
  obtain ⟨⟨a, p⟩, rfl⟩ := MetricGluing.point_surjective (fun a => P.planarCell a)
    (P.cutGlue cuts) x
  apply PolygonalPoint.ext
  change (P.restoreCut other (P.forgetCut cuts other included
    (MetricGluing.of (fun a => P.planarCell a) (P.cutGlue cuts) a p))).val =
      (P.restoreCut cuts (MetricGluing.of (fun a => P.planarCell a) (P.cutGlue cuts) a p)).val
  rw [P.forgetCut_of, P.restoreCut_of, P.restoreCut_of]

/-- Equal local horizontal cut germs preserve a whole ball about each actual metric bank copy.
The canonical map, rigid cell coordinates and all unbounded ends are retained. -/
theorem exists_forgetCut_ball_chart (cuts other : Set Plane) (included : other ⊆ cuts)
    (a : MetricGluing.Total (fun a => P.planarCell a)) {ε : ℝ} (positive : 0 < ε)
    (same : ∀ z, dist z (Cap.horizontal ((family (P.support a.1)).place a.2.val)) < ε →
      (z ∈ cuts ↔ z ∈ other)) :
    Nonempty (MetricGluing.ForgetChart (fun a => P.planarCell a)
      (P.cutGlue_mono cuts other included) a) := by
  let spatial_a : MetricGluing.Total (fun a => P.spatialCell a) :=
    ⟨a.1, P.cellIsometryEquiv a.1 a.2⟩
  have physical_same : ∀ z, dist z spatial_a.2.val < ε →
      (z ∈ Cap.horizontal ⁻¹' cuts ↔ z ∈ Cap.horizontal ⁻¹' other) := by
    intro z near
    apply same
    have projection : dist (Cap.horizontal z) (Cap.horizontal spatial_a.2.val) ≤
        dist z spatial_a.2.val := by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact Cap.horizontal_norm_le _
    exact projection.trans_lt near
  obtain ⟨chart⟩ := MetricGluing.exists_cutRestoreChart_of_local_eq P.spatialCell
    P.isClosed_spatialCell (Cap.horizontal ⁻¹' cuts) (Cap.horizontal ⁻¹' other)
    (Set.preimage_mono included) spatial_a positive physical_same
  let L := isometryEquivEBall (P.cutIsometryEquiv cuts)
    (MetricGluing.point (fun a => P.planarCell a) (P.cutGlue cuts) a)
    (ENNReal.ofReal chart.radius)
  let R := isometryEquivEBall (P.cutIsometryEquiv other)
    (MetricGluing.point (fun a => P.planarCell a) (P.cutGlue other) a)
    (ENNReal.ofReal chart.radius)
  let B := (L.trans chart.chart).trans R.symm
  refine ⟨⟨chart.radius, chart.positive, B, ?_⟩⟩
  intro x
  apply (P.cutIsometryEquiv other).injective
  change (P.cutIsometryEquiv other)
    ((P.cutIsometryEquiv other).symm (chart.chart (L x)).val) =
      P.cutIsometryEquiv other (P.forgetCut cuts other included x.val)
  rw [IsometryEquiv.apply_symm_apply, P.cutIsometryEquiv_forgetCut]
  exact chart.agrees (L x)

end Unfoldings.SpatialEnvelope.WholePartition
