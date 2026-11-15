module

public import Unfoldings.Geometry.SpatialEnvelopePartition
public import Unfoldings.Metric.PolygonalCutLocal
public import Unfoldings.Metric.PhysicalSeamsDiagonal

/-! Complete unbounded roof cuts with actual planar cells and exact uncut metric charts. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]

/-- The actual retained spatial attachments after a prescribed horizontal cut. -/
def cutPhysicalSeams (cuts : Set Plane) : MetricGluing.PhysicalSeams P.spatialCell :=
  MetricGluing.cutSeams P.spatialCell P.isClosed_spatialCell (Cap.horizontal ⁻¹' cuts)

/-- Physical retained attachments, in rigid planar coordinates, with same-cell seams omitted. -/
def cutGlue (cuts : Set Plane) :=
  MetricGluing.reparametrizeGlue P.cellIsometryEquiv (P.cutPhysicalSeams cuts).offDiagonal.relation

/-- The actual complete unbounded cut metric. Overlapping developments remain possible. -/
abbrev Cut (cuts : Set Plane) :=
  MetricGluing.Realization (fun a => P.planarCell a) (P.cutGlue cuts)

/-- Rigid coordinate changes and omitted identity seams preserve the exact cut metric. -/
def cutIsometryEquiv (cuts : Set Plane) :
    P.Cut cuts ≃ᵢ MetricGluing.PolygonalCut P.spatialCell P.isClosed_spatialCell
      (Cap.horizontal ⁻¹' cuts) :=
  (MetricGluing.reparametrizeIsometryEquiv P.cellIsometryEquiv
    (P.cutPhysicalSeams cuts).offDiagonal.relation).trans
    (P.cutPhysicalSeams cuts).offDiagonalIsometryEquiv

/-- Restore the cuts into the actual full intrinsic roof, retaining all unbounded ends. -/
def restoreCut (cuts : Set Plane) : P.Cut cuts → PolygonalPoint (wholeSurface family) :=
  MetricGluing.cutToPolygonal P.spatialCell P.isClosed_spatialCell (Cap.horizontal ⁻¹' cuts)
    P.convex_spatialCell P.wholeSurface_eq_iUnion_spatialCell ∘ P.cutIsometryEquiv cuts

@[simp] theorem restoreCut_of (cuts : Set Plane) (a : A) (x : P.planarCell a) :
    (P.restoreCut cuts (MetricGluing.of (fun a => P.planarCell a) (P.cutGlue cuts) a x)).val =
      (family (P.support a)).place x.val := rfl

theorem restoreCut_lipschitz (cuts : Set Plane) : LipschitzWith 1 (P.restoreCut cuts) := by
  simpa only [restoreCut, one_mul] using
    (MetricGluing.cutToPolygonal_lipschitz P.spatialCell P.isClosed_spatialCell
      (Cap.horizontal ⁻¹' cuts) P.convex_spatialCell P.wholeSurface_eq_iUnion_spatialCell).comp
      (P.cutIsometryEquiv cuts).isometry.lipschitzWith

theorem restoreCut_surjective (cuts : Set Plane) : Function.Surjective (P.restoreCut cuts) :=
  (MetricGluing.cutToPolygonal_surjective P.spatialCell P.isClosed_spatialCell
    (Cap.horizontal ⁻¹' cuts) P.convex_spatialCell P.wholeSurface_eq_iUnion_spatialCell).comp
    (P.cutIsometryEquiv cuts).surjective

theorem cut_complete (cuts : Set Plane) : CompleteSpace (P.Cut cuts) := by
  let : CompleteSpace (MetricGluing.PolygonalCut P.spatialCell P.isClosed_spatialCell
      (Cap.horizontal ⁻¹' cuts)) :=
    MetricGluing.polygonalCut_complete P.spatialCell P.isClosed_spatialCell
      (Cap.horizontal ⁻¹' cuts)
  exact (P.cutIsometryEquiv cuts).completeSpace

/-- Cutting removes actual seam declarations; it never introduces an interior attachment. -/
theorem cutGlue_subset (cuts : Set Plane) : ∀ x y, P.cutGlue cuts x y → P.glue x y := by
  intro x y joined
  have original := ((P.cutPhysicalSeams cuts).offDiagonal_relation_iff
    ⟨x.1, P.cellIsometryEquiv x.1 x.2⟩ ⟨y.1, P.cellIsometryEquiv y.1 y.2⟩).mp joined
  apply (P.glue_iff x y).mpr
  exact ⟨original.1, (P.cutPhysicalSeams cuts).physical_eq_of_eqvGen
    (Relation.EqvGen.rel _ _ original.2)⟩

theorem cut_seamSupport_boundary (cuts : Set Plane) (a : A) (x : P.planarCell a)
    (seam : x ∈ MetricGluing.seamSupport (fun a => P.planarCell a) (P.cutGlue cuts) a) :
    x.val ∉ interior (P.planarCell a) := by
  apply P.seamSupport_boundary a x
  rcases seam with ⟨y, joined⟩ | ⟨y, joined⟩
  · exact Or.inl ⟨y, P.cutGlue_subset cuts _ _ joined⟩
  · exact Or.inr ⟨y, P.cutGlue_subset cuts _ _ joined⟩

/-- The constructed roof projection is locally an exact whole-ball isometry away from cuts. -/
theorem exists_restoreCut_ball_isometry (cuts : Set Plane) (closed : IsClosed cuts)
    (x : P.Cut cuts) (outside : Cap.horizontal (P.restoreCut cuts x).val ∉ cuts) :
    ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball x (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (P.restoreCut cuts x) (ENNReal.ofReal r),
        ∀ y, (B y).val = P.restoreCut cuts y.val := by
  let S := P.cutPhysicalSeams cuts
  obtain ⟨a, ha⟩ := MetricGluing.point_surjective (fun a => P.spatialCell a) S.relation
    (P.cutIsometryEquiv cuts x)
  have position : (P.restoreCut cuts x).val = a.2.val := by
    change (MetricGluing.cutToPolygonal P.spatialCell P.isClosed_spatialCell
      (Cap.horizontal ⁻¹' cuts) P.convex_spatialCell P.wholeSurface_eq_iUnion_spatialCell
      (P.cutIsometryEquiv cuts x)).val = a.2.val
    rw [← ha]
    rfl
  have outside_a : a.2.val ∉ Cap.horizontal ⁻¹' cuts := by
    change Cap.horizontal a.2.val ∉ cuts
    rwa [← position]
  have result := MetricGluing.exists_cutToPolygonal_ball_isometry P.spatialCell
    P.isClosed_spatialCell (Cap.horizontal ⁻¹' cuts) P.convex_spatialCell
    P.wholeSurface_eq_iUnion_spatialCell (closed.preimage Cap.horizontalCLM.continuous) a outside_a
  change MetricGluing.point (fun a => P.spatialCell a)
    (MetricGluing.cutSeams P.spatialCell P.isClosed_spatialCell
      (Cap.horizontal ⁻¹' cuts)).relation a =
      P.cutIsometryEquiv cuts x at ha
  rw [ha] at result
  obtain ⟨r, positive, B, agrees⟩ := result
  let C := isometryEquivEBall (P.cutIsometryEquiv cuts) x (ENNReal.ofReal r)
  exact ⟨r, positive, C.trans B, fun y => agrees (C y)⟩

end Unfoldings.SpatialEnvelope.WholePartition
