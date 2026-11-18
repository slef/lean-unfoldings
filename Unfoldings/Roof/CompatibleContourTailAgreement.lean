module

public import Unfoldings.Roof.CompatibleContourTerminalMarks
public import Unfoldings.Geometry.BankGapTailJoin

/-! Actual terminal gap banks and roof continuations match as closed, equally paced banks. -/

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
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance contourTailAgreementIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "SourceAt[" q "," i "]" => TriangleComplex.contourOriginalVertex
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) q i
local notation "RetainAt[" q "," i "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut)
  (TriangleComplex.contourFrontier
    (SpatialEnvelope.Triangulation.pairedComplex
      (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
    (PotentialCutForest.selection Fcut) q i)

local notation "ChainAt[" q "," h "," i "," hf "," n "," hn "]" =>
  K.compatibleMeshFreshSourceBankChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute q h i hf n hn

local notation "cap" => SpatialEnvelope.Triangulation.normalizedCap
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "RollAt[" q "," h "," i "," hf "," n "," hn "]" => TriangleComplex.boundaryChainRoll
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) ChainAt[q,h,i,hf,n,hn]

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
local notation "LengthAt[" q "," e "]" => TriangleComplex.positiveContourBankLength D Selection q e
local notation "SpanAt[" q "," e "]" => TriangleComplex.positiveContourBank_span D Selection q e
local notation "VertexAt[" q "," e "]" => TriangleComplex.positiveContourVertex D Selection q e

local notation "BankAt[" q "," h "," e "]" =>
  K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e
local notation "OpenedAt[" q "," h "," e "]" =>
  K.compatibleContourOpenedBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e

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
      (K.compatibleContourOpenedBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance contourTailAgreementWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W

local notation "RootAt[" e "]" => K.compatibleMeshTerminalRoot compact nonempty R no_boundary
  level higher M positive inner_disk beta acute (Subtype.val e)
  (TriangleComplex.contourTerminalEdge_positive D Selection e)
local notation "EndAt[" e "," side "]" =>
  K.compatibleContourParentMark compact nonempty R no_boundary level higher M positive inner_disk
    beta acute contour starts W (Subtype.val e) (And.left (Subtype.property e)) side 1

local notation "GapMark[" v "," h "," e "," he "," side "," t "]" =>
  K.compatibleContourGapEdgeMark compact nonempty R no_boundary level higher M positive inner_disk
    beta acute contour starts models v h e he side t
local notation "ParentMark[" v "," h "," side "," t "]" =>
  K.compatibleContourParentMark compact nonempty R no_boundary level higher M positive inner_disk
    beta acute contour starts W v h side t
local notation "TailAt[" e "," side "," t "]" =>
  K.compatibleContourTerminalMark compact nonempty R no_boundary level higher M positive
    inner_disk beta acute contour starts W e side t

/-- Every finite-edge bank mark on a terminal stack is the gap's literal final edge point. -/
theorem compatibleContourGapEdgeMark_last
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection)
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (member : event ∈ (T).pairedComplex.contourSavedGapStack (Fcut).selection contour edge.val)
    (side : Bool) (t : unitInterval) :
    GapMark[edge.val,edge.property.1,event,member,side,t] =
      (models event).edgePoint side (Fin.last LengthAt[contour,event]) t := by
  unfold compatibleContourGapEdgeMark
  apply congrArg (fun k => (models event).edgePoint side k t)
  exact (T).pairedComplex.contourGapBankIndex_last (Fcut).selection contour edge event _

/-- Infinite gap-bank attachments begin at exactly their actual finite attachment endpoints. -/
theorem compatibleContourGapTail_join
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection)
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (member : event ∈ (T).pairedComplex.contourSavedGapStack (Fcut).selection contour edge.val)
    (side : Bool) :
    (models event).tailPoint side 0 =
      GapMark[edge.val,edge.property.1,event,member,side,1] :=
  ((models event).tailPoint_zero_eq_edgePoint side).trans
    (K.compatibleContourGapEdgeMark_last compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts models edge event member side 1).symm

/-- Every complete gap tail attaches with exactly the corresponding whole roof tail metric.
No normalization or terminal-side certificate is supplied. -/
theorem edist_compatibleContourGapTail
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection)
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (member : event ∈ (T).pairedComplex.contourSavedGapStack (Fcut).selection contour edge.val)
    (side : Bool) (s t : ℝ≥0) :
    edist ((models event).tailPoint side s) ((models event).tailPoint side t) =
      edist TailAt[edge,false,s] TailAt[edge,false,t] := by
  let bank := (T).pairedComplex.contourParentBank (Fcut).selection contour
    (Fcut).boundary_roots starts edge.val edge.property.1 false
  have finite_match := K.edist_compatibleContourGapEdgeMark compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W models edge.val edge.property.1
    event member side 0 1
  have first := K.compatibleContourGapEdgeMark_last compact nonempty R no_boundary level higher
    M positive inner_disk beta acute contour starts models edge event member side 0
  have last := K.compatibleContourGapEdgeMark_last compact nonempty R no_boundary level higher
    M positive inner_disk beta acute contour starts models edge event member side 1
  have finite_distance := (congrArg₂ edist first last).symm.trans finite_match
  have roof_finite := K.compatibleWholeMap_edist_bank compact nonempty R no_boundary level higher
    M positive inner_disk beta acute W bank 0 1
  have length := (T).pairedFolding.edist_directedBoundaryPath_eq_length bank 0 1
  have unit : edist (0 : unitInterval) 1 = 1 := by
    rw [edist_dist]
    change ENNReal.ofReal (dist (0 : ℝ) 1) = 1
    norm_num
  rw [unit, mul_one] at length
  have coefficient := finite_distance.trans (roof_finite.trans length)
  have roof_tail := K.edist_compatibleContourTerminalMark_eq_length compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W edge false s t
  exact ((models event).edist_tailPoint_eq_last_edge side s t).trans
    ((congrArg (fun d => d * edist s t) coefficient).trans roof_tail.symm)

end Unfoldings.ConvexRoof
