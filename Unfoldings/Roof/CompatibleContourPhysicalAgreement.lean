module

public import Unfoldings.Roof.CompatibleContourPhysicalBanks
public import Unfoldings.Polyhedron.RootwardSpatialChain

/-! Actual gap and roof attachments retain the same original spatial labels. -/

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

local instance contourPhysicalAgreementMeshFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "ChainAt[" q "," h "," i "," hf "," n "," hn "]" =>
  K.compatibleMeshFreshSourceBankChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute q h i hf n hn

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

local instance contourPhysicalAgreementWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Index" => K.compatibleContourCellIndex compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models

local notation "PhysicalAt[" e "]" => K.compatibleContourPhysicalBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "FoldAt[" e "]" => K.compatibleContourGapFrontierMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts models e
local notation "PositionAt[" vertex "]" => SpatialFolding.toSpace
  (SpatialEnvelope.Triangulation.pairedFolding
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) Set.univ
  (TriangleComplex.vertexPoint D Set.univ vertex)
local notation "IndexAt[" vertex "," nonroot "," event "," member "]" =>
  TriangleComplex.contourGapBankIndex D Selection contour vertex nonroot event
    (Iff.mpr (TriangleComplex.mem_contourEdgeGapStack D Selection contour vertex event)
      (Iff.mp (TriangleComplex.mem_contourSavedGapStack D Selection contour vertex event) member))
local notation "ParentAt[" vertex "," nonroot "," side "," time "]" =>
  K.compatibleContourParentMark compact nonempty R no_boundary level higher M positive inner_disk
    beta acute contour starts W vertex nonroot side time

/-- The physical source path keeps its original parent labels throughout each closed edge. -/
theorem compatibleContourPhysicalBank_point
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (k : Fin (LengthAt[contour,event] + 1)) (t : unitInterval) :
    (PhysicalAt[event]).chain.point k t =
      AffineMap.lineMap (PositionAt[(Fcut).parents.parent^[k.val] VertexAt[contour,event]])
        (PositionAt[(Fcut).parents.parent ((Fcut).parents.parent^[k.val] VertexAt[contour,event])])
        t.val :=
  (T).pairedFolding.boundarySpatialChain_rootward_point
    ChainAt[contour,starts,event.val,event.property.1,LengthAt[contour,event],SpanAt[contour,event]]
    VertexAt[contour,event] SpanAt[contour,event]
    (K.compatibleMeshFreshSourceBankChain_original compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts event.val event.property.1
      LengthAt[contour,event] SpanAt[contour,event])
    (K.compatibleMeshFreshSourceBankChain_terminal_original compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts event.val event.property.1
      LengthAt[contour,event] SpanAt[contour,event]) k t

/-- Every stack occurrence has exactly its named original physical parent-edge interpolation. -/
theorem compatibleContourPhysicalBank_parent_point
    (vertex : (T).pairedComplex.Vertex Set.univ) (nonroot : vertex ∉ (Fcut).parents.roots)
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (member : event ∈ (T).pairedComplex.contourSavedGapStack (Fcut).selection contour vertex)
    (t : unitInterval) :
    (PhysicalAt[event]).chain.point IndexAt[vertex,nonroot,event,member] t =
      AffineMap.lineMap PositionAt[vertex] PositionAt[(Fcut).parents.parent vertex] t.val := by
  have position := K.compatibleContourPhysicalBank_point compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts event
    IndexAt[vertex,nonroot,event,member] t
  have original := (T).pairedComplex.contourGapBankIndex_original (Fcut).selection contour vertex
    nonroot event
    ((T).pairedComplex.mem_contourEdgeGapStack (Fcut).selection contour vertex event |>.mpr
      ((T).pairedComplex.mem_contourSavedGapStack (Fcut).selection contour vertex event |>.mp
        member))
  exact position.trans (congrArg (fun v =>
    AffineMap.lineMap PositionAt[v] PositionAt[(Fcut).parents.parent v] t.val) original)

/-- Restoring either literal roof bank gives the same original spatial interpolation. -/
theorem restore_compatibleContourParentMark_position
    (vertex : (T).pairedComplex.Vertex Set.univ) (nonroot : vertex ∉ (Fcut).parents.roots)
    (side : Bool) (t : unitInterval) :
    (W.partition.restoreCut R.carrier ParentAt[vertex,nonroot,side,t]).val =
      AffineMap.lineMap PositionAt[vertex] PositionAt[(Fcut).parents.parent vertex] t.val :=
  (K.restore_compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W _).trans
    ((T).pairedFolding.contourParentBank_position (Fcut).selection contour (Fcut).boundary_roots
      starts vertex nonroot side t)

/-- Both sides of every gap-edge attachment have the original roof bank's physical label. -/
theorem compatibleContourGapFrontierMap_edge
    (vertex : (T).pairedComplex.Vertex Set.univ) (nonroot : vertex ∉ (Fcut).parents.roots)
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (geometry : OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (member : event ∈ (T).pairedComplex.contourSavedGapStack (Fcut).selection contour vertex)
    (side : Bool) (t : unitInterval) :
    (FoldAt[event] ((models event).addressFrontier side
      (.inl (IndexAt[vertex,nonroot,event,member], t)))).val =
        (W.partition.restoreCut R.carrier ParentAt[vertex,nonroot,false,t]).val :=
  (congrArg Subtype.val
    (K.compatibleContourGapFrontierMap_address compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts models event geometry side _)).trans
    ((K.compatibleContourPhysicalBank_parent_point compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts vertex nonroot event member t).trans
      (K.restore_compatibleContourParentMark_position compact nonempty R no_boundary level higher
        M positive inner_disk beta acute contour starts W vertex nonroot false t).symm)

end Unfoldings.ConvexRoof
