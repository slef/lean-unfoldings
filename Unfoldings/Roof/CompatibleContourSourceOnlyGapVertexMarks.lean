module

public import Unfoldings.Roof.CompatibleContourSourceOnlyGraftCells
public import Unfoldings.Roof.CompatibleContourGapMarkUniqueness
public import Unfoldings.Geometry.BankGapBendAddresses
public import Unfoldings.Cap.ContourLeafFans

/-! Actual source-only gap vertices keep their original incident attachment labels. -/

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

local instance contourGapVertexMarksFintype : Fintype (T).Index :=
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
  (models : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    BankGapModel
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
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
local notation "AddressAt[" b "," e "," h "," t "]" => K.compatibleContourGapAddress compact
  nonempty R no_boundary level higher M positive inner_disk beta acute contour b e h t

/-- A source-only mark has its original edge or tail address on the complemented gap side. -/
theorem compatibleContourSourceOnlyGapMark_address (bank : Attachment) (event : Event)
    (member : event ∈ Stack bank) (side : Bool) (t : ParamAt bank) :
    (Gap bank event member side t).val =
      ((models event).addressFrontier (!side) AddressAt[bank,event,member,t]).val := by
  cases bank <;> rfl

/-- A bend is reached only by the two adjacent finite parameters on its original bank. -/
theorem compatibleContourSourceOnlyGapMark_eq_bend (event : Event)
    (g : OrientedBankGap BankAt[event] MovedAt[event])
    (k : Fin LengthAt[event]) (side : Bool)
    (bank : Attachment) (member : event ∈ Stack bank) (other : Bool) (t : ParamAt bank)
    (same : Gap bank event member other t = (models event).edgePoint side k.succ 0) :
    (!other) = side ∧
      (AddressAt[bank,event,member,t] = .inl (k.castSucc, 1) ∨
        AddressAt[bank,event,member,t] = .inl (k.succ, 0)) := by
  have coordinate : (models event).addressFrontier (!other) AddressAt[bank,event,member,t] =
      (models event).addressFrontier side (.inl (k.succ, 0)) := by
    apply Subtype.ext
    exact (K.compatibleContourSourceOnlyGapMark_address compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts models bank event member other
      t).symm.trans (congrArg PolygonalPoint.val same)
  exact (models event).addressFrontier_eq_bend g
    (K.compatibleContourSourceOnlyBank_edge_ne_zero compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts models event) side (!other) k _ coordinate

/-- The common source is reached only by the two original bank starts. -/
theorem compatibleContourSourceOnlyGapMark_eq_source (event : Event)
    (g : OrientedBankGap BankAt[event] MovedAt[event])
    (bank : Attachment) (member : event ∈ Stack bank) (side : Bool) (t : ParamAt bank)
    (same : Gap bank event member side t = (models event).edgePoint false 0 0) :
    AddressAt[bank,event,member,t] = .inl (0, 0) := by
  have coordinate : (models event).addressFrontier (!side) AddressAt[bank,event,member,t] =
      (models event).addressFrontier false (.inl (0, 0)) := by
    apply Subtype.ext
    exact (K.compatibleContourSourceOnlyGapMark_address compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts models bank event member side
      t).symm.trans (congrArg PolygonalPoint.val same)
  exact (models event).address_eq_source g
    (K.compatibleContourSourceOnlyBank_edge_ne_zero compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts models event) (!side) _ coordinate

local notation "SourceAt[" e "]" => TriangleComplex.positiveContourVertex D Selection contour e
local notation "FirstEdge[" e "]" => (Sum.inl
  (Subtype.mk SourceAt[e] (TriangleComplex.positiveContourVertex_nonroot D Selection contour e)) :
    Attachment)

/-- Both literal source attachment sides give the same intrinsic tip of the actual gap. -/
theorem compatibleContourSourceOnlyGapMark_at_source (event : Event)
    (g : OrientedBankGap BankAt[event] MovedAt[event])
    (member : event ∈ Stack FirstEdge[event]) (side : Bool) :
    Gap FirstEdge[event] event member side 0 = (models event).edgePoint false 0 0 := by
  let v := SourceAt[event]
  let nonroot := (D).positiveContourVertex_nonroot Selection contour event
  have at_edge : event ∈ (D).contourEdgeGapStack Selection contour v :=
    ((D).mem_contourEdgeGapStack Selection contour v event).mpr
      (((D).mem_contourSavedGapStack Selection contour v event).mp member)
  have index := (D).contourGapBankIndex_source Selection contour event at_edge
  change (models event).edgePoint (!side)
    ((D).contourGapBankIndex Selection contour v nonroot event at_edge) 0 = _
  refine (congrArg (fun i => (models event).edgePoint (!side) i 0) index).trans ?_
  cases side
  · apply PolygonalPoint.ext
    have tip : ((models event).edgePoint true 0 0).val = (MovedAt[event]).start := by
      rw [BankGapModel.edgePoint_val, PolygonalChain.point_zero, Fin.castSucc_zero]
      rfl
    have old : ((models event).edgePoint false 0 0).val = (BankAt[event]).start := by
      rw [BankGapModel.edgePoint_val, PolygonalChain.point_zero, Fin.castSucc_zero]
      rfl
    exact tip.trans (g.common.trans old.symm)
  · rfl

/-- Every mark incident to the common source uses exactly its original first finite attachment. -/
theorem compatibleContourSourceOnlyGapMark_eq_source_attachment (event : Event)
    (g : OrientedBankGap BankAt[event] MovedAt[event])
    (member : event ∈ Stack FirstEdge[event]) (bank : Attachment)
    (other_member : event ∈ Stack bank) (side : Bool) (t : ParamAt bank)
    (same : Gap bank event other_member side t = (models event).edgePoint false 0 0) :
    (⟨bank, t⟩ : Σ b : Attachment, ParamAt b) = ⟨FirstEdge[event], 0⟩ := by
  have source_index := K.compatibleContourSourceOnlyGapMark_eq_source compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts models
    event g bank other_member side t same
  have named : AddressAt[FirstEdge[event],event,member,0] = .inl (0, 0) :=
    congrArg (fun i => Sum.inl (i, (0 : unitInterval)))
      ((D).contourGapBankIndex_source Selection contour event _)
  exact K.compatibleContourGapAddress_eq compact nonempty R no_boundary level higher M positive
    inner_disk beta acute contour event FirstEdge[event] bank member other_member 0 t
    (source_index.trans named.symm)

end Unfoldings.ConvexRoof
