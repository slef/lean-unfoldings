module

public import Unfoldings.FewestNets.ThreeExitGraftLabels
public import Unfoldings.Complex.ContourGapBankSurjectivity
public import Unfoldings.Metric.ClosedSeamsContinuousLift

/-! The entire unbounded ordered graft collapses properly to its original spatial roof. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : FewestNets.ThreeExitStemWindows}
  {R : K.ThreeExitComponentRouting seed B compact nonempty H}

local notation "U" => K.selectionComponent slopes seed
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ K.restrictedCarrier U}
local notation "G" => SlopeEnvelope.recenter
  (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty) B.reference
local notation "pointOf" => (fun v : V => K.projectedVertex (Subtype.val v))

variable {level : ℝ}
  {M : (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty).FiniteSlopeModel}
  (L : R.FloorWindowModel level M)

local notation "T[" h "]" => R.fineMesh level M h
local notation "D[" h "]" => SpatialEnvelope.FloorMesh.pairedComplex T[h]
local notation "F[" h "]" => R.fineMeshForest level M h
local notation "Sel[" h "]" => PotentialCutForest.selection F[h]

local instance graftCollapseIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
    Fintype (T[h]).Index := @Fintype.ofFinite _ (T[h]).finite

variable (S : SourceContour (R := R) (M := M) (level := level))

local notation "T" => T[S.higher]
local notation "D" => D[S.higher]
local notation "Fcut" => F[S.higher]
local notation "Selection" => Sel[S.higher]
local notation "Event" => TriangleComplex.PositiveContourSource D Selection S.contour
local notation "Model[" e "]" => OrientedBankGap.model (S.gaps e)
local notation "Pieces" => polygonalBankStackPiece L.whole.Cut (fun e : Event => BankGapModel.region (Model[e]))
local notation "Stack" => PotentialCutForest.contourAttachmentStack Fcut S.contour
local notation "Base" => contourBaseMark L S
local notation "Gap" => PotentialCutForest.contourGapMark Fcut S.contour S.starts
  (fun e : Event => Model[e])
local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap

local notation "Index" => contourGraftCellIndex L S
local notation "Cells" => contourGraftCells L S
local notation "Inner" => contourGraftCellInner L S
local notation "Coordinates" => contourGraftCellCoordinates L S
local notation "Raw" => MetricGluing.NestedCell (fun i j => Cells i j)
local notation "Attachment" => PotentialCutForest.ContourAttachment Fcut
local notation "Param" => PotentialCutForest.contourAttachmentParameter Fcut

local notation "restore" =>
  SpatialEnvelope.WholePartition.restoreCut L.whole.partition R.wholeCarrier
local notation "Path[" e "]" => PotentialCutForest.contourSourceSpatialRay Fcut S.contour S.starts e
local notation "Fold" => contourGraftPieceCollapse L S
local notation "Seams" => contourGraftClosedSeams L S
local notation "original" => MetricGluing.mappedNestedPoint Cells Inner Coordinates
local notation "Label" => Space ⊕ (Event × ℂ)

local notation "LabelAt" => contourGraftPieceLabel L S
local notation "CellLabel" => contourGraftCellLabel L S
local notation "FrontierAt" => contourGraftFrontierLabel L S
local notation "Graft" => contourGraft L S
local notation "Banks" => MetricGluing.bankSeams Left Right
local notation "Surface" => SpatialEnvelope.wholeSurface M.plane

/-- Every address of an actual gap is a literal physical point of a named original bank. -/
theorem exists_contourGraftSourcePath_baseMark (e : Event) {x : Space}
    (member : x ∈ (Path[e]).carrier) :
    ∃ (a : Attachment) (t : Param a), (restore (Base a false t)).val = x := by
  obtain ⟨a, at_x⟩ := (Path[e]).exists_address member
  cases a with
  | inl b =>
    obtain ⟨i, t⟩ := b
    obtain ⟨v, nonroot, edge_member, eq⟩ :=
      (D).exists_contourGapBankIndex_eq Selection S.contour e i
    let a : Attachment := .inl ⟨v, nonroot⟩
    have saved : e ∈ Stack a :=
      ((D).mem_contourSavedGapStack Selection S.contour v e).mpr
        (((D).mem_contourEdgeGapStack Selection S.contour v e).mp edge_member)
    have at_gap : Fold (some e) (Gap a e saved false t) = (Path[e]).chain.point i t := by
      change (R.contourSourceGapCollapse level M S.higher S.contour S.starts e (S.gaps e)
        (Model[e].edgePoint true
          ((D).contourGapBankIndex Selection S.contour v nonroot e edge_member) t)).val = _
      rw [R.contourSourceGapCollapse_edgePoint, eq]
    have there := (L.contourGraftPieceCollapse_gap_eq S a e saved false t).symm.trans at_gap
    exact ⟨a, t, there.trans at_x⟩
  | inr t =>
    obtain ⟨edge, saved⟩ := (D).exists_contourTerminalEdge_mem_gapStack Selection S.contour e
    let a : Attachment := .inr edge
    have at_gap : Fold (some e) (Gap a e saved false t) = (Path[e]).tail t := by
      change (R.contourSourceGapCollapse level M S.higher S.contour S.starts e
        (S.gaps e) (Model[e].tailPoint true t)).val = _
      rw [R.contourSourceGapCollapse_tailPoint]
    have there := (L.contourGraftPieceCollapse_gap_eq S a e saved false t).symm.trans at_gap
    exact ⟨a, t, there.trans at_x⟩

include L in
/-- Every actual physical gap address lands in the original whole roof. -/
theorem contourGraftSourcePath_subset_surface (e : Event) : (Path[e]).carrier ⊆ Surface := by
  intro x member
  obtain ⟨a, t, hx⟩ := L.exists_contourGraftSourcePath_baseMark S e member
  exact hx ▸ (restore (Base a false t)).property

open Classical in
private def labelSpatial : Label → Space
  | .inl x => x
  | .inr (e, z) =>
    if hz : z ∈ Model[e].region then Fold (some e) ⟨z, hz⟩ else 0

private theorem labelSpatial_pieceLabel (i : Option Event) (p : Pieces i) :
    L.labelSpatial S (LabelAt i p) = Fold i p := by
  classical
  cases i with
  | none => rfl
  | some e =>
    change L.labelSpatial S (MetricGluing.partialLabel (frontier Model[e].region)
      (FrontierAt e) e p.val) = Fold (some e) p
    by_cases boundary : p.val ∈ frontier Model[e].region
    · rw [MetricGluing.partialLabel_of_mem _ _ _ _ boundary]
      rfl
    · unfold MetricGluing.partialLabel
      rw [dite_eq_right boundary]
      change (if h : p.val ∈ Model[e].region then Fold (some e) ⟨p.val, h⟩ else 0) = _
      rw [dite_eq_left p.property]
      rfl

set_option maxHeartbeats 1300000 in
-- The proper lift is taken from the exact closed-seam quotient.
/-- The collapse descends from its exact original piece maps. Its image is the
whole original roof, and all seam identifications have the named physical image. -/
theorem exists_contourGraftProperCollapse :
    ∃ f : Graft → Space, IsProperMap f ∧ Set.range f = Surface ∧
      ∀ y : MetricGluing.Total Pieces, f (MetricGluing.point Pieces Banks y) = Fold y.1 y.2 := by
  let maps (ij : Σ i, Index i) (x : Raw ij) :=
    let y := original ⟨ij, x⟩
    Fold y.1 y.2
  have labeled (x : MetricGluing.Total Raw) : L.labelSpatial S (CellLabel x) = maps x.1 x.2 :=
    L.labelSpatial_pieceLabel S (original x).1 (original x).2
  have compatible (x y : MetricGluing.Total Raw) (glued : (Seams).relation x y) :
      maps x.1 x.2 = maps y.1 y.2 := (labeled x).symm.trans
    ((congrArg (L.labelSpatial S) (L.contourGraftCellLabel_seam S x y glued)).trans (labeled y))
  let finite := L.finite_contourGraftClosedSeams_class S
  let E := L.contourGraftClosedSeamsIsometry S
  let f := (Seams).continuousLift finite maps compatible ∘ E.symm
  have on_piece (y : MetricGluing.Total Pieces) :
      f (MetricGluing.point Pieces Banks y) = Fold y.1 y.2 := by
    obtain ⟨x, rfl⟩ := MetricGluing.mappedNestedPoint_surjective Cells Inner Coordinates y
    have image : E (MetricGluing.point Raw (Seams).relation x) =
        MetricGluing.point Pieces Banks (original x) := rfl
    have before := (congrArg E.symm image).symm.trans (E.symm_apply_apply _)
    change (Seams).continuousLift finite maps compatible
      (E.symm (MetricGluing.point Pieces Banks (original x))) = _
    rw [before, MetricGluing.ClosedSeams.continuousLift_point]
  have onto : Set.range f = Surface := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨⟨i, p⟩, rfl⟩ := MetricGluing.point_surjective Pieces Banks x
      have image := on_piece ⟨i, p⟩
      cases i with
      | none => exact image.symm ▸ (restore p).property
      | some e =>
        exact image.symm ▸ L.contourGraftSourcePath_subset_surface S e
          (R.contourSourceGapCollapse level M S.higher S.contour S.starts e (S.gaps e) p).property
    · intro x member
      obtain ⟨p, equal⟩ := L.whole.partition.restoreCut_surjective R.wholeCarrier ⟨x, member⟩
      exact ⟨MetricGluing.point Pieces Banks ⟨none, p⟩,
        (on_piece ⟨none, p⟩).trans (congrArg PolygonalPoint.val equal)⟩
  exact ⟨f, ((Seams).isProperMap_continuousLift finite maps compatible
    (L.isProperMap_contourGraftCellCollapse S)).comp E.symm.toHomeomorph.isProperMap, onto, on_piece⟩

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
