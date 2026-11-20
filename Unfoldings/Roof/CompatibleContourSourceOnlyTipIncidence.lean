module

public import Unfoldings.Roof.CompatibleContourSourceOnlyGapVertexMarks
public import Unfoldings.Roof.CompatibleContourFiniteSeamClasses
public import Unfoldings.Metric.BankStackAdjacentGaps

/-! The two original source bank slots are the only seams incident to a gap tip. -/

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

local instance sourceOnlyTipIncidenceIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlyTipIncidenceWholeFintype : Fintype W.Index := W.finiteIndex

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
local notation "FiniteBank[" v "," h "]" => (Sum.inl (Subtype.mk v h) : Attachment)
local notation "Addr" => MetricGluing.BankStackAddress (G := Event) (Parameter := ParamAt)
local notation "Named" => MetricGluing.bankStackEndpointAddress (Parameter := ParamAt) Stack
local notation "Mark" => MetricGluing.bankStackAddressPoint Stack Pieces Base Gap
local notation "Valid" => MetricGluing.BankStackAddressValid Stack
local notation "EndAt" => MetricGluing.bankStackEndpoint Stack Pieces Base Gap
local notation "L" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Rgt" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams L Rgt
local notation "Time" => (Σ s : MetricGluing.BankStackSlot Stack, ParamAt (Sigma.fst s))

local notation "BankAt[" e "]" => K.compatibleContourSourceBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "MovedAt[" e "]" => K.compatibleContourSourceOnlyBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e


local notation "Edge" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Interval[" v "," h "]" => TriangleComplex.contourParentInterval
  D Selection contour (PotentialCutForest.boundary_roots Fcut) starts v h
local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W
local notation "Retain" => PotentialCutForest.retain Fcut
local notation "SourceOf[" e "]" => TriangleComplex.positiveContourVertex D Selection contour e
local notation "RoofPoint[" j "]" => (Sigma.mk none (Map
  (TriangleComplex.vertexPoint D Retain (TriangleComplex.boundaryEndVertex D Retain
    (PairedInvolutions.System.Chain.point (TriangleComplex.BoundaryContour.cycle contour) j)))) :
      MetricGluing.Total Pieces)




local notation "SourceEdge[" e "]" => FiniteBank[SourceOf[e],
  TriangleComplex.positiveContourVertex_nonroot D Selection contour e]

set_option maxHeartbeats 950000 in
-- Named tip slots and the intrinsic source position use the same dependent address.
/-- The two literally named slots at a source are exactly the incidences of its gap tip. -/
theorem compatibleContourSourceOnlyTip_endpoint_iff (event : Event)
    (g : OrientedBankGap BankAt[event] MovedAt[event]) (member : event ∈ Stack SourceEdge[event])
    (first last : Time)
    (first_name : Named true first.1 first.2 = ⟨SourceEdge[event], some event, false, 0⟩)
    (last_name : Named false last.1 last.2 = ⟨SourceEdge[event], some event, true, 0⟩)
    (side : Bool) (s : Time) :
    EndAt side s.1 s.2 = ⟨some event, (models event).edgePoint false 0 0⟩ ↔
      (side = true ∧ s = first) ∨ (side = false ∧ s = last) := by
  let a := SourceEdge[event]
  let tip : MetricGluing.Total Pieces := ⟨some event, (models event).edgePoint false 0 0⟩
  have nodup := K.compatibleContourBankStack_nodup compact nonempty R no_boundary level higher
    M positive inner_disk beta acute contour
  have recover (addr : Addr) (valid : Valid addr) (eq : Mark addr valid = tip) :
      addr = ⟨a, some event, false, 0⟩ ∨ addr = ⟨a, some event, true, 0⟩ := by
    obtain ⟨bank, tag, flag, time⟩ := addr
    cases tag with
    | none => cases congrArg Sigma.fst eq
    | some e =>
      have named : e = event := Option.some.inj (congrArg Sigma.fst eq)
      subst e
      have raw : Gap bank event valid flag time = (models event).edgePoint false 0 0 :=
        eq_of_heq (Sigma.mk.inj eq).2
      have at_source := K.compatibleContourSourceOnlyGapMark_eq_source_attachment compact nonempty
        R no_boundary level higher M positive inner_disk beta acute contour starts models
        event g member bank valid flag time raw
      let f (u : Σ e : Attachment, ParamAt e) : Addr := ⟨u.1, some event, flag, u.2⟩
      have exact_name : (⟨bank, some event, flag, time⟩ : Addr) = ⟨a, some event, flag, 0⟩ :=
        congrArg f at_source
      cases flag
      · exact Or.inl exact_name
      · exact Or.inr exact_name
  constructor
  · intro eq
    let addr := Named side s.1 s.2
    let valid := MetricGluing.bankStackEndpointAddress_valid Stack side s.1 s.2
    have at_mark : Mark addr valid = tip :=
      (MetricGluing.bankStackAddressPoint_endpoint Stack Pieces Base Gap side s.1 s.2).trans eq
    rcases recover addr valid at_mark with head | tail
    · have same : (side, s) = (true, first) :=
        MetricGluing.bankStackEndpointAddress_injective Stack nodup (head.trans first_name.symm)
      exact Or.inl ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩
    · have same : (side, s) = (false, last) :=
        MetricGluing.bankStackEndpointAddress_injective Stack nodup (tail.trans last_name.symm)
      exact Or.inr ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩
  · rintro (⟨side_eq, time_eq⟩ | ⟨side_eq, time_eq⟩)
    · rw [side_eq, time_eq]
      exact (MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap true first
        a event member false 0 first_name).trans (congrArg (Sigma.mk (some event))
          (K.compatibleContourSourceOnlyGapMark_at_source compact nonempty R no_boundary level
            higher M positive inner_disk beta acute contour starts models event g member false))
    · rw [side_eq, time_eq]
      exact (MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap false last
        a event member true 0 last_name).trans (congrArg (Sigma.mk (some event))
          (K.compatibleContourSourceOnlyGapMark_at_source compact nonempty R no_boundary level
            higher M positive inner_disk beta acute contour starts models event g member true))

end Unfoldings.ConvexRoof
