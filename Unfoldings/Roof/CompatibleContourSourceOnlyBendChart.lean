module

public import Unfoldings.Cone.DirectedIntervalChart
public import Unfoldings.Geometry.OrientedBankGapBendChart
public import Unfoldings.Roof.CompatibleContourSourceOnlyGaps
public import Unfoldings.Roof.CompatibleContourBendAngles
public import Unfoldings.Roof.CompatibleContourBankAgreement

/-! The actual source-only bend charts have the saved-frontier fan and its complement. -/

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

local instance sourceOnlyBendChartIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "SourceAt[" q "," i "]" => TriangleComplex.contourOriginalVertex
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) q i
local notation "ChainAt[" q "," h "," i "," hf "," n "," hn "]" =>
  K.compatibleMeshFreshSourceBankChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute q h i hf n hn

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
local notation "LengthAt[" q "," e "]" => TriangleComplex.positiveContourBankLength D Selection q e
local notation "SpanAt[" q "," e "]" => TriangleComplex.positiveContourBank_span D Selection q e
local notation "VertexAt[" q "," e "]" => TriangleComplex.positiveContourVertex D Selection q e

local notation "Event[" q "]" => TriangleComplex.PositiveContourSource D Selection q
local notation "BankAt[" q "," h "," e "]" =>
  K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e
local notation "MovedAt[" q "," h "," e "]" =>
  K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
    inner_disk beta acute q h e

local notation "FrontierAt[" q "," i "]" => TriangleComplex.contourFrontier D Selection q i
local notation "RetainAt[" q "," i "]" => TriangleComplex.processedParentRetain D Selection
  FrontierAt[q,i]

/-- A literal oriented bend has the unchanged saved-frontier angle on the first bank
and its full-turn complement on the rotated bank. The resulting whole local chart
retains the original two planar edge directions. -/
theorem compatibleContourSourceOnlyGap_bend_sector_chart
    (contour : (T).pairedComplex.BoundaryContour
      ((T).pairedComplex.selectedRetain (Fcut).selection))
    (starts : SourceAt[contour,0] ∈ (Fcut).parents.roots)
    (event : Event[contour])
    (G : OrientedBankGap BankAt[contour,starts,event] MovedAt[contour,starts,event])
    (k : Fin (LengthAt[contour,event])) (side : Bool)
    (strict : let first := BankAt[contour,starts,event]
      0 < inner ℝ (first.chain.vertex k.succ.castSucc - first.start) (first.chain.edge k.succ)) :
    let bank := G.model.bank side
    let p := bank.chain.vertex k.succ.castSucc
    let incoming := bank.chain.edge k.castSucc
    let outgoing := bank.chain.edge k.succ
    let retain := RetainAt[contour,event.val.succ]
    let chain := ChainAt[contour,starts,event.val,event.property.1,LengthAt[contour,event],
      SpanAt[contour,event]]
    let saved := (D).totalAngle retain ((D).boundaryEndVertex retain (chain.point k.succ))
    let θ := if side then 2 * Real.pi - saved else saved
    let frame := if side then radialRightCornerFrame (p - bank.start) incoming
      else radialLeftCornerFrame (p - bank.start) outgoing
    let x := G.model.edgePoint side k.succ 0
    ∃ (pos : 0 < θ) (r : ℝ), 0 < r ∧
      ∃ A : Metric.eball x (ENNReal.ofReal r) ≃ᵢ
          Metric.eball (closedAngularSectorOrigin pos.le) (ENNReal.ofReal r),
        ∀ y, p + frame (A y).val.val = y.val.val := by
  let B := BankAt[contour,starts,event]
  let κ := (D).interiorAngularDefect Set.univ VertexAt[contour,event]
  let bank := G.model.bank side
  let p := bank.chain.vertex k.succ.castSucc
  let frame := if side then radialRightCornerFrame (p - bank.start) (bank.chain.edge k.castSucc)
    else radialLeftCornerFrame (p - bank.start) (bank.chain.edge k.succ)
  let retain := RetainAt[contour,event.val.succ]
  let chain := ChainAt[contour,starts,event.val,event.property.1,LengthAt[contour,event],
    SpanAt[contour,event]]
  let saved := (D).totalAngle retain ((D).boundaryEndVertex retain (chain.point k.succ))
  let θ := if side then 2 * Real.pi - saved else saved
  let width := if side then
    radialRightCornerWidth (p - bank.start)
      (bank.chain.edge k.castSucc) (bank.chain.edge k.succ)
    else radialLeftCornerWidth (p - bank.start)
      (bank.chain.edge k.castSucc) (bank.chain.edge k.succ)
  have genuine (i : Fin (LengthAt[contour,event] + 1)) : B.chain.edge i ≠ 0 := by
    apply norm_ne_zero_iff.mp
    have speed := K.compatibleContourSourceBank_edge_length compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts event i
    exact speed.trans_ne ((D).boundaryBankLength_pos _).ne'
  have nonzero (i : Fin (LengthAt[contour,event] + 1)) : bank.chain.edge i ≠ 0 := by
    cases side
    · exact genuine i
    · change (B.rotateSuffix 0 κ).chain.edge i ≠ 0
      rw [B.rotateSuffix_zero_edge]
      simpa only [map_zero] using (complexRotation κ).injective.ne (genuine i)
  have radial : 0 < inner ℝ (p - bank.start) (bank.chain.edge k.succ) := by
    cases side
    · exact strict
    · change 0 < inner ℝ ((B.rotateSuffix 0 κ).chain.vertex k.succ.castSucc -
        (B.rotateSuffix 0 κ).start) ((B.rotateSuffix 0 κ).chain.edge k.succ)
      rw [B.rotateSuffix_zero_vertex_sub_start, B.rotateSuffix_zero_edge,
        LinearIsometry.inner_map_map]
      exact strict
  have first := K.compatibleContourSourceBank_first_bend_aperture compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts event k G.first_outward strict
  have same : width = θ := by
    cases side
    · exact first
    · let Q := B.rotateSuffix 0 κ
      let right := radialRightCornerWidth (Q.chain.vertex k.succ.castSucc - Q.start)
        (Q.chain.edge k.castSucc) (Q.chain.edge k.succ)
      have balance : saved + right = 2 * Real.pi :=
        (congrArg (fun a => a + right) first.symm).trans
          (PolygonalRay.sourceOpening_corner_widths_add (B := B) κ k)
      change right = 2 * Real.pi - saved
      linarith only [balance]
  obtain ⟨pos, small, r, rpos, A, _, physical⟩ := G.exists_model_bend_chart side k nonzero radial
  have θpos : 0 < θ := same ▸ pos
  let F := bisectedSectorFan width pos small
  have angle : F.totalAngle = θ := (bisectedSectorFan_totalAngle width pos small).trans same
  let E := (F.intrinsicAngularSectorIsometryEquiv (angle.trans_lt (same ▸ small))).trans
    (PolygonalPoint.congrIsometryEquiv (congrArg closedAngularSector angle))
  have center : E F.origin = closedAngularSectorOrigin θpos.le := by
    apply PolygonalPoint.ext
    rw [IsometryEquiv.trans_apply, PolygonalPoint.congrIsometryEquiv_val,
      AngularFan.intrinsicAngularSectorIsometryEquiv_val, AngularFan.develop_origin]
    rfl
  refine ⟨θpos, r, rpos, A.trans (basedEBallIsometry E F.origin _ center (ENNReal.ofReal r)), ?_⟩
  intro y
  change p + frame (E (A y).val).val = _
  rw [IsometryEquiv.trans_apply, PolygonalPoint.congrIsometryEquiv_val,
    AngularFan.intrinsicAngularSectorIsometryEquiv_val]
  exact physical y

end Unfoldings.ConvexRoof
