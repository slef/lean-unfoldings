module

public import Unfoldings.FewestNets.ThreeExitGraftFiniteCoverage
public import Unfoldings.FewestNets.ThreeExitGraftTerminalCoverage
public import Unfoldings.FewestNets.ThreeExitGraftProperCollapse
public import Unfoldings.Roof.PotentialContourGapAddress

/-! All copies of the cut and the gap fibers carry the same original bank addresses. -/

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

local instance graftAddressCoverageIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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
local notation "Attachment" => PotentialCutForest.ContourAttachment Fcut
local notation "Param" => PotentialCutForest.contourAttachmentParameter Fcut

local notation "restore" =>
  SpatialEnvelope.WholePartition.restoreCut L.whole.partition R.wholeCarrier
local notation "Path[" e "]" => PotentialCutForest.contourSourceSpatialRay Fcut S.contour S.starts e
local notation "Fold" => contourGraftPieceCollapse L S
local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Graft" => contourGraft L S
local notation "Banks" => MetricGluing.bankSeams Left Right

/-- The finite parent banks and their continued tails exhaust the entire cut. -/
theorem contourBaseMark_range_eq_cut :
    (⋃ a : Attachment, ⋃ side : Bool, Set.range (Base a side)) =
      {x | Cap.horizontal (restore x).val ∈ R.wholeCarrier} := by
  ext x
  constructor
  · intro named
    obtain ⟨a, on_attachment⟩ := Set.mem_iUnion.mp named
    obtain ⟨side, t, rfl⟩ := Set.mem_iUnion.mp on_attachment
    exact L.contourGraftBaseMark_horizontal_mem_cut S a side t
  · intro cut
    have names : ∃ (a : Attachment) (side : Bool) (t : Param a), Base a side t = x := by
      rcases lt_or_ge ((G).height (Cap.horizontal (restore x).val)) level with below | above
      · obtain ⟨v, side, t, equal⟩ := L.exists_contourParentMark_of_cut_below S x cut below
        exact ⟨.inl v, side, t, equal⟩
      · obtain ⟨v, side, t, equal⟩ := L.exists_contourTailMark_of_cut_above S x cut above
        exact ⟨.inr v, side, t, equal⟩
    obtain ⟨a, side, t, equal⟩ := names
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨side, t, equal⟩⟩

/-- The actual graft collapse restricts to the exact marked arc fibers on every gap. -/
theorem hasMarkedCollapseFibers_contourGraft (f : Graft → Space)
    (on_piece : ∀ y : MetricGluing.Total Pieces,
      f (MetricGluing.point Pieces Banks y) = Fold y.1 y.2) (e : Event) :
    Model[e].HasMarkedCollapseFibers (Path[e])
      (fun x => f (MetricGluing.point Pieces Banks ⟨some e, x⟩)) := by
  have agrees : (fun x => f (MetricGluing.point Pieces Banks ⟨some e, x⟩)) =
      Fold (some e) := funext (fun x => on_piece ⟨some e, x⟩)
  have marked : Model[e].HasMarkedCollapseFibers (Path[e]) (Fold (some e)) :=
    R.hasMarkedCollapseFibers_contourSourceGapCollapse level M
      S.higher S.contour S.starts e (S.gaps e)
  exact Eq.mp (congrArg (Model[e].HasMarkedCollapseFibers (Path[e])) agrees.symm) marked

/-- The physical marks used by the ordered attachment seams are precisely the
two endpoints of the arc fiber over the same address. -/
theorem contourGraftGapMark_eq_intrinsicAddressPoint (a : Attachment) (e : Event)
    (saved : e ∈ Stack a) (side : Bool) (t : Param a) :
    Gap a e saved side t =
      Model[e].intrinsicAddressPoint (!side)
        (PotentialCutForest.contourGapAddress Fcut S.contour a e saved t) := by
  cases a <;> cases side <;> rfl

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
