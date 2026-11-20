module

public import Unfoldings.Geometry.SourceGapFibers
public import Unfoldings.Roof.CompatibleContourPhysicalOrder
public import Unfoldings.Complex.ContourGapBankSurjectivity

public import Unfoldings.Geometry.SourceGapPhysicalCollapse
public import Unfoldings.Geometry.BankGapClosedEmbeddings
public import Unfoldings.Metric.ClosedSeamsContinuousLift
public import Unfoldings.Roof.CompatibleContourSourceOnlyLabels

/-! Collapse the actual entire source-only graft to the original spatial roof. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)
  (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
  (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ slopes)
  (beta : 0 ≤ β) (acute : β < Real.pi / 2)

local notation "T" => K.compatibleCutMesh compact nonempty R no_boundary level higher M
  positive inner_disk
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance sourceOnlyCollapseGraftIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
variable (contour :
    (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.BoundaryContour
    ((K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.selectedRetain
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection))
  (starts : (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.contourOriginalVertex
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour 0 ∈
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).parents.roots)
  (W : R.WholeCutModel M)
  (models : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    BankGapModel
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance sourceOnlyCollapseGraftWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Pieces" => polygonalBankStackPiece W.Cut
  (fun event : Event => BankGapModel.region (models event))
local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "Gap" => K.compatibleContourSourceOnlyGapMark compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts models

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "LengthAt[" e "]" => TriangleComplex.positiveContourBankLength D Selection contour e
local notation "BankAt[" e "]" => K.compatibleContourSourceBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "MovedAt[" e "]" => K.compatibleContourSourceOnlyBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "SpatialAt[" e "]" => K.compatibleContourPhysicalBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "Index" => K.compatibleContourSourceOnlyCellIndex compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "Cells" => K.compatibleContourSourceOnlyCells compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts W models
local notation "Inner" => K.compatibleContourSourceOnlyCellInner compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "Coordinates" => K.compatibleContourSourceOnlyCellCoordinates compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts W models
local notation "Raw" => MetricGluing.NestedCell (fun i j => Cells i j)
local notation "Seams" => K.compatibleContourSourceOnlyClosedSeams compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

local notation "Graft" => K.compatibleContourSourceOnlyGraft compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "Label" => Space ⊕ (Event × ℂ)
local notation "CellLabel" => K.compatibleContourSourceOnlyCellLabel compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "FoldAt[" e "]" => K.compatibleContourSourceOnlyFrontierMap compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts models e
local notation "L" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Rgt" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams L Rgt

local notation "Surface" => SpatialEnvelope.wholeSurface M.plane

include W in
/-- The physical reference bank of any gap is entirely on the original full roof. -/
theorem compatibleContourPhysicalBank_subset_wholeSurface (e : Event) :
    (SpatialAt[e]).carrier ⊆ Surface := by
  intro x mem
  obtain ⟨address, position⟩ := (SpatialAt[e]).exists_address mem
  cases address with
  | inl q =>
    obtain ⟨i, t⟩ := q
    obtain ⟨v, nonroot, member, eq⟩ := (D).exists_contourGapBankIndex_eq Selection contour e i
    let bank : Attachment := .inl ⟨v, nonroot⟩
    let physical := W.partition.restoreCut R.carrier (Base bank false t)
    have named_member : e ∈ Stack bank :=
      ((D).mem_contourSavedGapStack Selection contour v e).mpr
        (((D).mem_contourEdgeGapStack Selection contour v e).mp member)
    have named := K.compatibleContourPhysicalBank_parent_point compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts v nonroot e named_member t
    have restored := K.restore_compatibleContourParentMark_position compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W v nonroot false t
    have step : (SpatialAt[e]).chain.point i t = physical.val :=
      (congrArg (fun j => (SpatialAt[e]).chain.point j t) eq).symm.trans
        (named.trans restored.symm)
    exact (step.symm.trans position) ▸ physical.property
  | inr t =>
    obtain ⟨edge, member⟩ := (D).exists_contourTerminalEdge_mem_gapStack Selection contour e
    let bank : Attachment := .inr edge
    let physical := W.partition.restoreCut R.carrier (Base bank false t)
    have named := K.compatibleContourPhysicalBank_tail_parent compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W edge e member t
    have restored := K.restore_compatibleContourTerminalMark_affine compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W edge false t
    have step : (SpatialAt[e]).tail t = physical.val := named.trans restored.symm
    exact (step.symm.trans position) ▸ physical.property

/-- The proper spatial collapse has image exactly the original full roof and
preserves every original bank mark. Each nonempty restriction of a fiber to an
individual gap is contractible. -/
theorem compatibleContourSourceOnlyGraft_exists_proper_collapse_range_with_gap_fibers
    (geometry : ∀ e : Event, OrientedBankGap BankAt[e] MovedAt[e])
    (matched : ∀ e, models e = (geometry e).model) :
    ∃ f : Graft → Space, IsProperMap f ∧ Set.range f = Surface ∧
      (∀ x : W.Cut, f (MetricGluing.point Pieces Banks ⟨none, x⟩) =
        (W.partition.restoreCut R.carrier x).val) ∧
      (∀ (e : Event) (x : PolygonalPoint (models e).region)
        (boundary : x.val ∈ frontier (models e).region),
        f (MetricGluing.point Pieces Banks ⟨some e, x⟩) =
          (FoldAt[e] ⟨x.val, boundary⟩).val) ∧
      ∀ (e : Event) (x : PolygonalPoint (models e).region),
        ContractibleSpace {y | f (MetricGluing.point Pieces Banks ⟨some e, y⟩) =
          f (MetricGluing.point Pieces Banks ⟨some e, x⟩)} := by
  classical
  have gap_exists (e : Event) :
      ∃ f : PolygonalPoint (models e).region → Space, IsProperMap f ∧
        Set.range f ⊆ (SpatialAt[e]).carrier ∧
        (∀ (x : PolygonalPoint (models e).region) (h : x.val ∈ frontier (models e).region),
          f x = (FoldAt[e] ⟨x.val, h⟩).val) ∧
        ∀ x, ContractibleSpace {y | f y = f x} := by
    let g := geometry e
    let predicate (model : BankGapModel BankAt[e] MovedAt[e]) : Prop :=
      ∃ f : PolygonalPoint model.region → Space, IsProperMap f ∧
        Set.range f ⊆ (SpatialAt[e]).carrier ∧
        (∀ (x : PolygonalPoint model.region) (h : x.val ∈ frontier model.region),
          f x = (model.frontierMap SpatialAt[e] ⟨x.val, h⟩).val) ∧
        ∀ x, ContractibleSpace {y | f y = f x}
    have genuine (side : Bool) (i : Fin (LengthAt[e] + 1)) :
        ((models e).bank side).chain.edge i ≠ 0 :=
      K.compatibleContourSourceOnlyBank_edge_ne_zero compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts models e side i
    have target_ne : (SpatialAt[e]).direction ≠ 0 :=
      K.compatibleContourPhysicalBank_direction_ne_zero compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts e
    have closedEmbedding := ((SpatialAt[e]).isClosed_carrier target_ne).isClosedEmbedding_subtypeVal
    have faithful := K.compatibleContourPhysicalBank_mapCarrier_injective compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W e BankAt[e]
      g.first_outward (genuine false) g.first_nonzero
    have proof : predicate g.model :=
      ⟨fun x => (g.collapseTo SpatialAt[e] x).val,
        closedEmbedding.isProperMap.comp
          (g.isProperMap_collapseTo SpatialAt[e] (genuine false) target_ne),
        (by rintro _ ⟨x, rfl⟩; exact (g.collapseTo SpatialAt[e] x).property),
        fun x boundary => congrArg Subtype.val
          (g.collapseTo_eq_frontierMap SpatialAt[e] (genuine false) (genuine true) x boundary),
        fun x => g.contractibleSpace_collapseTo_fiber SpatialAt[e] faithful x⟩
    change predicate (models e)
    exact Eq.mpr (congrArg predicate (matched e)) proof
  choose fold fold_proper fold_range fold_boundary fold_fiber using gap_exists
  let piece : ∀ i, Pieces i → Space
    | none => fun x => (W.partition.restoreCut R.carrier x).val
    | some e => fold e
  let coordinate : Label → Space
    | .inl p => p
    | .inr (e, z) => if h : z ∈ (models e).region then fold e ⟨z, h⟩ else 0
  have label_agrees (x : MetricGluing.Total Pieces) :
      coordinate (K.compatibleContourSourceOnlyPieceLabel compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W models x.1 x.2) =
          piece x.1 x.2 := by
    obtain ⟨i, x⟩ := x
    cases i with
    | none => rfl
    | some e =>
      change coordinate (MetricGluing.partialLabel (frontier (models e).region)
        (fun z => (FoldAt[e] z).val) e x.val) = fold e x
      by_cases boundary : x.val ∈ frontier (models e).region
      · rw [MetricGluing.partialLabel_of_mem _ _ _ _ boundary]
        exact (fold_boundary e x boundary).symm
      · have interior_label : MetricGluing.partialLabel (frontier (models e).region)
            (fun z => (FoldAt[e] z).val) e x.val = .inr (e, x.val) := by
          unfold MetricGluing.partialLabel
          exact dite_eq_right boundary
        rw [interior_label]
        change (if h : x.val ∈ (models e).region then fold e ⟨x.val, h⟩ else 0) = _
        exact dite_eq_left x.property
  let original := MetricGluing.mappedNestedPoint Cells Inner Coordinates
  let maps (ij : Σ i, Index i) (x : Raw ij) :=
    let y := original ⟨ij, x⟩
    piece y.1 y.2
  have maps_proper (ij : Σ i, Index i) : IsProperMap (maps ij) := by
    obtain ⟨i, j⟩ := ij
    cases i with
    | none =>
      let : CompleteSpace (Raw ⟨none, j⟩) := by
        change CompleteSpace (W.partition.planarCell j)
        exact (W.partition.isClosed_planarCell j).isComplete.completeSpace_coe
      have isometric : Isometry (maps ⟨none, j⟩) := by
        intro x y
        change edist (W.partition.restoreCut R.carrier (MetricGluing.of _ _ j x)).val
          (W.partition.restoreCut R.carrier (MetricGluing.of _ _ j y)).val = edist x y
        exact (congrArg₂ (fun u v : Space => edist u v)
          (W.partition.restoreCut_of R.carrier j x)
          (W.partition.restoreCut_of R.carrier j y)).trans
            ((M.plane (W.partition.support j)).place.isometry.edist_eq x.val y.val)
      exact isometric.isClosedEmbedding.isProperMap
    | some e =>
      exact (fold_proper e).comp ((models e).planarCell_intrinsic_isClosedEmbedding j).isProperMap
  have agrees (x : MetricGluing.Total Raw) : coordinate (CellLabel x) = maps x.1 x.2 :=
    label_agrees (original x)
  have compatible (x y : MetricGluing.Total Raw) (seam : (Seams).relation x y) :
      maps x.1 x.2 = maps y.1 y.2 :=
    (agrees x).symm.trans ((congrArg coordinate
      (K.compatibleContourSourceOnlyCellLabel_seam compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W models geometry x y seam)).trans
        (agrees y))
  let finite := K.compatibleContourSourceOnlyClosedSeams_finite_classes compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W models geometry
  let E := K.compatibleContourSourceOnlyClosedSeamsIsometry compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models
  let f := (Seams).continuousLift finite maps compatible ∘ E.symm
  have on_piece (y : MetricGluing.Total Pieces) :
      f (MetricGluing.point Pieces Banks y) = piece y.1 y.2 := by
    obtain ⟨x, rfl⟩ := MetricGluing.mappedNestedPoint_surjective Cells Inner Coordinates y
    have image : E (MetricGluing.point Raw (Seams).relation x) =
        MetricGluing.point Pieces Banks (original x) := rfl
    have pre := (congrArg E.symm image).symm.trans (E.symm_apply_apply _)
    change (Seams).continuousLift finite maps compatible
      (E.symm (MetricGluing.point Pieces Banks (original x))) = _
    rw [pre, MetricGluing.ClosedSeams.continuousLift_point]
  have onto : Set.range f = Surface := by
    apply Set.Subset.antisymm
    · rintro x ⟨q, rfl⟩
      obtain ⟨⟨i, y⟩, rfl⟩ := MetricGluing.point_surjective Pieces Banks q
      have equal := on_piece ⟨i, y⟩
      cases i with
      | none => exact equal.symm ▸ (W.partition.restoreCut R.carrier y).property
      | some e =>
        have in_path := fold_range e (Set.mem_range_self y)
        exact equal.symm ▸ K.compatibleContourPhysicalBank_subset_wholeSurface compact nonempty R
          no_boundary level higher M positive inner_disk beta acute contour starts W e in_path
    · intro x inside
      obtain ⟨y, eq⟩ := W.partition.restoreCut_surjective R.carrier ⟨x, inside⟩
      exact ⟨MetricGluing.point Pieces Banks ⟨none, y⟩,
        (on_piece ⟨none, y⟩).trans (congrArg PolygonalPoint.val eq)⟩
  refine ⟨f, ((Seams).isProperMap_continuousLift finite maps compatible maps_proper).comp
    E.symm.toHomeomorph.isProperMap, onto, fun x => on_piece ⟨none, x⟩,
    fun e x boundary => (on_piece ⟨some e, x⟩).trans (fold_boundary e x boundary), ?_⟩
  intro e x
  have named (y : PolygonalPoint (models e).region) :
      f (MetricGluing.point Pieces Banks ⟨some e, y⟩) = fold e y := on_piece ⟨some e, y⟩
  have equal : {y | f (MetricGluing.point Pieces Banks ⟨some e, y⟩) =
      f (MetricGluing.point Pieces Banks ⟨some e, x⟩)} = {y | fold e y = fold e x} := by
    ext y
    change f (MetricGluing.point Pieces Banks ⟨some e, y⟩) =
      f (MetricGluing.point Pieces Banks ⟨some e, x⟩) ↔ fold e y = fold e x
    rw [named x, named y]
  rw [equal]
  exact fold_fiber e x

/-- The proper spatial collapse has image exactly the original full roof and
preserves every original bank mark. -/
theorem compatibleContourSourceOnlyGraft_exists_proper_collapse_range
    (geometry : ∀ e : Event, OrientedBankGap BankAt[e] MovedAt[e])
    (matched : ∀ e, models e = (geometry e).model) :
    ∃ f : Graft → Space, IsProperMap f ∧ Set.range f = Surface ∧
      (∀ x : W.Cut, f (MetricGluing.point Pieces Banks ⟨none, x⟩) =
        (W.partition.restoreCut R.carrier x).val) ∧
      ∀ (e : Event) (x : PolygonalPoint (models e).region)
        (boundary : x.val ∈ frontier (models e).region),
        f (MetricGluing.point Pieces Banks ⟨some e, x⟩) =
          (FoldAt[e] ⟨x.val, boundary⟩).val := by
  obtain ⟨f, proper, range_eq, roof, banks, _⟩ :=
    K.compatibleContourSourceOnlyGraft_exists_proper_collapse_range_with_gap_fibers compact nonempty
      R no_boundary level higher M positive inner_disk beta acute contour starts W models
      geometry matched
  exact ⟨f, proper, range_eq, roof, banks⟩

/-- The original spatial restoration and all named gap banks agree with a proper
map on the entire intrinsic graft. -/
theorem compatibleContourSourceOnlyGraft_exists_proper_collapse
    (geometry : ∀ e : Event, OrientedBankGap BankAt[e] MovedAt[e])
    (matched : ∀ e, models e = (geometry e).model) :
    ∃ f : Graft → Space, IsProperMap f ∧
      (∀ x : W.Cut, f (MetricGluing.point Pieces Banks ⟨none, x⟩) =
        (W.partition.restoreCut R.carrier x).val) ∧
      ∀ (e : Event) (x : PolygonalPoint (models e).region)
        (boundary : x.val ∈ frontier (models e).region),
        f (MetricGluing.point Pieces Banks ⟨some e, x⟩) =
          (FoldAt[e] ⟨x.val, boundary⟩).val := by
  obtain ⟨f, proper, _, roof, gap⟩ := K.compatibleContourSourceOnlyGraft_exists_proper_collapse_range
    compact nonempty R no_boundary level higher M positive inner_disk beta acute contour starts
    W models geometry matched
  exact ⟨f, proper, roof, gap⟩

/-- The same physical collapse is continuous on the whole graft, with every original bank. -/
theorem compatibleContourSourceOnlyGraft_exists_continuous_collapse
    (geometry : ∀ e : Event, OrientedBankGap BankAt[e] MovedAt[e])
    (matched : ∀ e, models e = (geometry e).model) :
    ∃ f : Graft → Space, Continuous f ∧
      (∀ x : W.Cut, f (MetricGluing.point Pieces Banks ⟨none, x⟩) =
        (W.partition.restoreCut R.carrier x).val) ∧
      ∀ (e : Event) (x : PolygonalPoint (models e).region)
        (boundary : x.val ∈ frontier (models e).region),
        f (MetricGluing.point Pieces Banks ⟨some e, x⟩) =
          (FoldAt[e] ⟨x.val, boundary⟩).val := by
  obtain ⟨f, proper, roof, gap⟩ := K.compatibleContourSourceOnlyGraft_exists_proper_collapse
    compact nonempty R no_boundary level higher M positive inner_disk beta acute contour starts
    W models geometry matched
  exact ⟨f, proper.continuous, roof, gap⟩

/-- Horizontal projection of the physical collapse is a proper surjection to the
original projected plane, with the prescribed values on the original roof and gap banks. -/
theorem compatibleContourSourceOnlyGraft_exists_proper_planar_collapse
    (geometry : ∀ e : Event, OrientedBankGap BankAt[e] MovedAt[e])
    (matched : ∀ e, models e = (geometry e).model) :
    ∃ f : Graft → Plane, IsProperMap f ∧ Function.Surjective f ∧
      (∀ x : W.Cut, f (MetricGluing.point Pieces Banks ⟨none, x⟩) =
        Cap.horizontal (W.partition.restoreCut R.carrier x).val) ∧
      ∀ (e : Event) (x : PolygonalPoint (models e).region)
        (boundary : x.val ∈ frontier (models e).region),
        f (MetricGluing.point Pieces Banks ⟨some e, x⟩) =
          Cap.horizontal (FoldAt[e] ⟨x.val, boundary⟩).val := by
  obtain ⟨f, proper, range_eq, roof, gaps⟩ :=
    K.compatibleContourSourceOnlyGraft_exists_proper_collapse_range compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W models
      geometry matched
  let spatial (z : Graft) : Surface := ⟨f z, range_eq ▸ Set.mem_range_self z⟩
  have spatial_proper : IsProperMap spatial :=
    isProperMap_of_comp_of_inj (proper.continuous.subtype_mk _)
      continuous_subtype_val proper Subtype.val_injective
  have onto (p : Surface) : ∃ z, spatial z = p := by
    obtain ⟨z, exact_val⟩ : p.val ∈ Set.range f := range_eq.symm ▸ p.property
    exact ⟨z, Subtype.ext exact_val⟩
  let H := SpatialEnvelope.wholeSurfaceHomeomorph M.plane
  exact ⟨H ∘ spatial, H.isProperMap.comp spatial_proper, H.surjective.comp onto,
    fun x => congrArg Cap.horizontal (roof x),
    fun e x boundary => congrArg Cap.horizontal (gaps e x boundary)⟩

end Unfoldings.ConvexRoof
