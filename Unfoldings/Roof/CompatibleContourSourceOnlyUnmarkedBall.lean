module

public import Unfoldings.Roof.CompatibleWholeCutRegularity
public import Unfoldings.Roof.CompatibleContourSourceOnlyLabels
public import Unfoldings.Metric.BankStackUnmarkedBall

/-! Whole graft balls away from the actual roof banks and gap frontiers. -/

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

local instance sourceOnlyUnmarkedBallIndexFintype : Fintype (T).Index :=
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
  (geometry : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    OrientedBankGap
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance sourceOnlyUnmarkedBallWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "models" => (fun event : Event => OrientedBankGap.model (geometry event))
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
local notation "Valid" => MetricGluing.BankStackAddressValid Stack
local notation "Named" => MetricGluing.bankStackEndpointAddress (Parameter := ParamAt) Stack
local notation "Mark" => MetricGluing.bankStackAddressPoint Stack Pieces Base Gap
local notation "EndAt" => MetricGluing.bankStackEndpoint Stack Pieces Base Gap
local notation "L" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Rgt" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams L Rgt
local notation "Addr" => MetricGluing.BankStackAddress (G := Event) (Parameter := ParamAt)
local notation "Point" => MetricGluing.point Pieces Banks

local notation "IndexAt[" v "," h "," e "," member "]" =>
  TriangleComplex.contourGapBankIndex D Selection contour v h e
    (Iff.mpr (TriangleComplex.mem_contourEdgeGapStack D Selection contour v e)
      (Iff.mp (TriangleComplex.mem_contourSavedGapStack D Selection contour v e) member))

private theorem compatibleContourSourceOnly_hasMetricBallChart_of_no_address
    {Y : Type*} [MetricSpace Y] (a : MetricGluing.Total Pieces)
    (regular : HasMetricBallChart Y a.2)
    (unmarked : ∀ (addr : Addr) (valid : Valid addr), Mark addr valid ≠ a) :
    HasMetricBallChart Y (Point a) := by
  obtain ⟨r, rpos, cover⟩ := K.compatibleContourSourceOnlyGraft_piece_ball_cover compact
    nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W models geometry a
  have no_end (side : Bool) (slot : MetricGluing.BankStackSlot Stack) (t : ParamAt slot.1) :
      EndAt side slot t ≠ a := by
    rw [← MetricGluing.bankStackAddressPoint_endpoint Stack Pieces Base Gap side slot t]
    exact unmarked (Named side slot t) _
  exact MetricGluing.bankStack_hasMetricBallChart_of_unmarked Pieces Stack Base Gap a regular
    (fun slot t => ⟨no_end false slot t, no_end true slot t⟩)
    (K.compatibleContourSourceOnlyBaseMark_isClosedEmbedding compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W)
    (K.compatibleContourSourceOnlyGapMark_isClosedEmbedding compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts models) rpos cover

/-- An original roof point off the physical cut has its original planar ball in the graft. -/
theorem compatibleContourSourceOnly_roof_off_cut_chart (convex : Convex ℝ slopes)
    (x : W.Cut) (off_cut : Cap.horizontal (W.partition.restoreCut R.carrier x).val ∉ R.carrier) :
    HasMetricBallChart Plane (Point ⟨none, x⟩) := by
  apply K.compatibleContourSourceOnly_hasMetricBallChart_of_no_address compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W geometry ⟨none, x⟩
  · exact K.compatibleWholeCut_off_cut_regular compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W convex x off_cut
  · rintro ⟨bank, gapTag, side, t⟩ valid h
    cases gapTag with
    | some g =>
      have impossible : some g = none := congrArg Sigma.fst h
      contradiction
    | none =>
      have h' : Base bank side t = x := eq_of_heq (Sigma.mk.inj h).2
      apply off_cut
      rw [← h']
      cases bank with
      | inl v =>
        exact K.compatibleContourParentMark_carrier compact nonempty R no_boundary level higher M
          positive inner_disk beta acute contour starts W v.val v.property side t
      | inr e =>
        exact K.compatibleContourTerminalMark_carrier compact nonempty R no_boundary level higher M
          positive inner_disk beta acute contour starts W e side t

/-- Every interior point of a gap has a planar ball, including points on its internal cell seams. -/
theorem compatibleContourSourceOnly_gap_interior_chart (e : Event)
    (x : PolygonalPoint (models e).region) (inside : x.val ∈ interior (models e).region) :
    HasMetricBallChart ℂ (Point ⟨some e, x⟩) := by
  apply K.compatibleContourSourceOnly_hasMetricBallChart_of_no_address compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W geometry ⟨some e, x⟩
  · obtain ⟨r, pos, covers⟩ := Metric.isOpen_iff.mp isOpen_interior x.val inside
    exact PolygonalPoint.hasMetricBallChart_of_ball pos (covers.trans interior_subset)
  · rintro ⟨bank, gapTag, side, t⟩ valid h
    cases gapTag with
    | none =>
      have impossible : (none : Option Event) = some e := congrArg Sigma.fst h
      contradiction
    | some g =>
      have tag : some g = some e := congrArg Sigma.fst h
      have same : g = e := Option.some.inj tag
      subst g
      have marked : Gap bank e valid side t = x := eq_of_heq (Sigma.mk.inj h).2
      have boundary : x.val ∈ frontier (models e).region := by
        rw [← marked]
        cases bank with
        | inl v =>
          exact ((models e).addressFrontier (!side)
            (.inl (IndexAt[v.val,v.property,e,valid], t))).property
        | inr b => exact ((models e).addressFrontier (!side) (.inr t)).property
      exact boundary.2 inside

end Unfoldings.ConvexRoof
