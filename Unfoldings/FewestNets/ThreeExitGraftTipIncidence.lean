module

public import Unfoldings.FewestNets.ThreeExitGraftStrictFiber
public import Unfoldings.Roof.PotentialContourGapVertexMarks
public import Unfoldings.Metric.BankStackAdjacentGaps


/-! Both original source marks name the same gap tip. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel

open MetricGluing

universe u v

set_option maxHeartbeats 1800000

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

local instance graftTipIncidenceIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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

local notation "FiniteBank[" v "," h "]" => (Sum.inl (Subtype.mk v h) : Attachment)
local notation "Retain" => PotentialCutForest.retain Fcut
local notation "EndAt" => MetricGluing.bankStackEndpoint Stack Pieces Base Gap
local notation "Time" => (Σ s : MetricGluing.BankStackSlot Stack, Param (Sigma.fst s))

local notation "Named" => MetricGluing.bankStackEndpointAddress (Parameter := Param) Stack
local notation "Addr" => MetricGluing.BankStackAddress («G» := Event) (Parameter := Param)
local notation "Valid" => MetricGluing.BankStackAddressValid Stack
local notation "Mark" => MetricGluing.bankStackAddressPoint Stack Pieces Base Gap
local notation "SourceOf[" e "]" => TriangleComplex.positiveContourVertex D Selection S.contour e
local notation "SourceEdge[" e "]" => (Sum.inl (Subtype.mk SourceOf[e]
  (TriangleComplex.positiveContourVertex_nonroot D Selection S.contour e)) : Attachment)
local notation "BankAt[" e "]" => PotentialCutForest.contourSourceRay Fcut S.contour S.starts e
local notation "MovedAt[" e "]" => PotentialCutForest.contourSourceOpenedRay Fcut S.contour S.starts e
local notation "models" => (fun e : Event => Model[e])
local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams Left Right
/-- The two literally named slots at a source are exactly the incidences of its gap tip. -/
theorem contourGraftTip_endpoint_iff (event : Event)
    (_g : OrientedBankGap BankAt[event] MovedAt[event]) (member : event ∈ Stack SourceEdge[event])
    (first last : Time)
    (first_name : Named true first.1 first.2 = ⟨SourceEdge[event], some event, false, 0⟩)
    (last_name : Named false last.1 last.2 = ⟨SourceEdge[event], some event, true, 0⟩)
    (side : Bool) (s : Time) :
    EndAt side s.1 s.2 = ⟨some event, (models event).edgePoint false 0 0⟩ ↔
      (side = true ∧ s = first) ∨ (side = false ∧ s = last) := by
  let a := SourceEdge[event]
  let tip : MetricGluing.Total Pieces := ⟨some event, (models event).edgePoint false 0 0⟩
  have nodup := contourGraft_stack_nodup S
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
      have at_source := (Fcut).contourGapMark_eq_source_attachment S.contour S.starts S.gaps
        event member bank valid flag time raw
      let f (u : Σ e : Attachment, Param e) : Addr := ⟨u.1, some event, flag, u.2⟩
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
          ((Fcut).contourGapMark_at_source S.contour S.starts S.gaps event member false))
    · rw [side_eq, time_eq]
      exact (MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap false last
        a event member true 0 last_name).trans (congrArg (Sigma.mk (some event))
          ((Fcut).contourGapMark_at_source S.contour S.starts S.gaps event member true))

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
