module

public import Unfoldings.Geometry.SpatialEnvelopeFaceSideCutPoints
public import Unfoldings.Geometry.SpatialEnvelopeCutClassSide
public import Unfoldings.Metric.ClosedSubcoverBall

/-! Original one-sided roof regions contain whole intrinsic bank balls. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]

/-- The physical cut coordinates and original intrinsic restoration have the same spatial point. -/
theorem fold_cutIsometryEquiv (cuts : Set Plane) (x : P.Cut cuts) :
    (P.cutPhysicalSeams cuts).fold (P.cutIsometryEquiv cuts x) = (P.restoreCut cuts x).val := by
  obtain ⟨⟨a, p⟩, rfl⟩ := MetricGluing.point_surjective (fun a => P.planarCell a) (P.cutGlue cuts) x
  change (P.cutPhysicalSeams cuts).fold
    (P.cutIsometryEquiv cuts (MetricGluing.of (fun a => P.planarCell a) (P.cutGlue cuts) a p)) =
      (P.restoreCut cuts (MetricGluing.of (fun a => P.planarCell a) (P.cutGlue cuts) a p)).val
  rw [P.cutIsometryEquiv_of, P.restoreCut_of, MetricGluing.PhysicalSeams.fold_of]
  rfl

variable (anchor : A) (f : Plane →ᵃ[ℝ] ℝ) (proper : f ≠ 0) (signs : A → Bool)
  (aligned : ∀ a x, x ∈ P.footprint a → 0 ≤ AffineArrangement.signed f (signs a) x)
  (cuts : Set Plane) (cut_closed : IsClosed cuts) (cut_level : ∀ x ∈ cuts, f x = 0)

/-- Every spatial point of each selected original cell has its exact original bank copy
in the canonical one-sided region image, including all original cell boundary points. -/
theorem faceSideRegionMap_covers_spatial_cell (a : P.FaceSideIndex anchor signs)
    (y : P.spatialCell a.val) :
    ∃ z : PolygonalPoint
        ((family (P.support anchor)).project.symm '' P.faceSideRegion anchor f signs),
      P.cutIsometryEquiv cuts
        (P.faceSideRegionMap anchor f proper signs aligned cuts cut_closed cut_level z) =
      MetricGluing.of (fun a => P.spatialCell a) (P.cutPhysicalSeams cuts).relation a.val y := by
  let B := P.faceSideCutIsometryEquiv anchor f proper signs aligned cuts cut_closed cut_level
  let raw := (P.cellIsometryEquiv a.val).symm y
  let x := P.faceSideCellIsometryEquiv anchor signs a raw
  let c : P.FaceSideCut anchor signs cuts :=
    MetricGluing.of (fun a => P.faceSideCell anchor signs a)
    (MetricGluing.cutSeams (P.faceSideCell anchor signs) (P.isClosed_faceSideCell anchor signs)
      ((family (P.support anchor)).place ⁻¹' (Cap.horizontal ⁻¹' cuts))).relation a x
  refine ⟨B c, ?_⟩
  change P.cutIsometryEquiv cuts (P.faceSideCutMap anchor signs cuts (B.symm (B c))) = _
  rw [B.symm_apply_apply]
  dsimp only [c]
  rw [P.faceSideCutMap_of, P.cutIsometryEquiv_of]
  change MetricGluing.of (fun a => P.spatialCell a) (P.cutPhysicalSeams cuts).relation a.val
    (P.cellIsometryEquiv a.val ((P.faceSideCellIsometryEquiv anchor signs a).symm
      (P.faceSideCellIsometryEquiv anchor signs a raw))) = _
  rw [IsometryEquiv.symm_apply_apply]
  change MetricGluing.of (fun a => P.spatialCell a) (P.cutPhysicalSeams cuts).relation a.val
    (P.cellIsometryEquiv a.val ((P.cellIsometryEquiv a.val).symm y)) = _
  rw [IsometryEquiv.apply_symm_apply]

/-- Local two-face geometry and the actual cut line force a whole intrinsic ball into
this original face-side region. Incident-cell supports and ball coverage are derived. -/
theorem exists_faceSideRegionMap_ball_chart
    (source : PolygonalPoint
      ((family (P.support anchor)).project.symm '' P.faceSideRegion anchor f signs))
    {U : Set Plane} (open_U : IsOpen U) (cut_line : ∀ z ∈ U, f z = 0 → z ∈ cuts)
    (inside : Cap.horizontal ((family (P.support anchor)).place source.val) ∈ U)
    {δ : ℝ} (positive : 0 < δ)
    (local_face : ∀ z, dist z (Cap.horizontal ((family (P.support anchor)).place source.val)) < δ →
      0 ≤ AffineArrangement.signed f (signs anchor) z →
        height family z = (family (P.support anchor)).height z) :
    ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball source (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (P.faceSideRegionMap anchor f proper signs aligned cuts cut_closed cut_level
        source)
        (ENNReal.ofReal r),
      ∀ z, (B z).val =
        P.faceSideRegionMap anchor f proper signs aligned cuts cut_closed cut_level z.val := by
  let F := P.cutIsometryEquiv cuts ∘
    P.faceSideRegionMap anchor f proper signs aligned cuts cut_closed cut_level
  have isometric : Isometry F := (P.cutIsometryEquiv cuts).isometry.comp
    (P.faceSideRegionMap_isometry anchor f proper signs aligned cuts cut_closed cut_level)
  let C := P.faceSideCutIsometryEquiv anchor f proper signs aligned cuts cut_closed cut_level
  obtain ⟨⟨i, x⟩, represents⟩ :=
    MetricGluing.point_surjective (fun a => P.faceSideCell anchor signs a)
    (MetricGluing.cutSeams (P.faceSideCell anchor signs) (P.isClosed_faceSideCell anchor signs)
      ((family (P.support anchor)).place ⁻¹' (Cap.horizontal ⁻¹' cuts))).relation (C.symm source)
  let raw := (P.faceSideCellIsometryEquiv anchor signs i).symm x
  let a : MetricGluing.Total (fun a => P.spatialCell a) :=
    ⟨i.val, P.cellIsometryEquiv i.val raw⟩
  let S := P.cutPhysicalSeams cuts
  have center : F source = MetricGluing.point (fun a => P.spatialCell a) S.relation a := by
    change P.cutIsometryEquiv cuts (P.faceSideCutMap anchor signs cuts (C.symm source)) = _
    rw [← represents]
    change P.cutIsometryEquiv cuts (P.faceSideCutMap anchor signs cuts
      (MetricGluing.of (fun a => P.faceSideCell anchor signs a)
        (MetricGluing.cutSeams (P.faceSideCell anchor signs) (P.isClosed_faceSideCell anchor signs)
          ((family (P.support anchor)).place ⁻¹' (Cap.horizontal ⁻¹' cuts))).relation i x)) = _
    rw [P.faceSideCutMap_of, P.cutIsometryEquiv_of]
    rfl
  have physical : a.2.val = (family (P.support anchor)).place source.val := by
    have same := congrArg S.fold center
    have restored :
        (P.restoreCut cuts
          (P.faceSideRegionMap anchor f proper signs aligned cuts cut_closed cut_level
            source)).val =
        a.2.val := (P.fold_cutIsometryEquiv cuts _).symm.trans same
    exact restored.symm.trans
      (P.restoreCut_faceSideRegionMap anchor f proper signs aligned cuts cut_closed cut_level
        source)
  have covered : ∀ j, (MetricGluing.classIn (fun a => P.spatialCell a) S.relation a j).Nonempty →
      ∀ y : P.spatialCell j, ∃ z,
        F z = MetricGluing.of (fun a => P.spatialCell a) S.relation j y := by
    intro j incident y
    obtain ⟨q, related⟩ := incident
    have selected := P.cutClass_mem_faceSideIndex anchor cuts f signs aligned open_U cut_line
      (by simpa only [physical] using inside) i.property.2 related positive
      (by simpa only [physical] using local_face)
    exact P.faceSideRegionMap_covers_spatial_cell anchor f proper signs aligned cuts cut_closed
      cut_level ⟨j, selected⟩ y
  have result := S.closedSeams.exists_isometric_subcover_ball a
    (fun j => (S.classIn_subsingleton a j).finite) F isometric source center covered
  rw [← center] at result
  obtain ⟨r, rpos, B, agrees⟩ := result
  let R := isometryEquivEBall (P.cutIsometryEquiv cuts)
    (P.faceSideRegionMap anchor f proper signs aligned cuts cut_closed cut_level source)
    (ENNReal.ofReal r)
  refine ⟨r, rpos, B.trans R.symm, ?_⟩
  intro z
  apply (P.cutIsometryEquiv cuts).injective
  change (P.cutIsometryEquiv cuts) ((P.cutIsometryEquiv cuts).symm (B z).val) = _
  exact ((P.cutIsometryEquiv cuts).apply_symm_apply (B z).val).trans (agrees z)

end Unfoldings.SpatialEnvelope.WholePartition
