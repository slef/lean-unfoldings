module

public import Unfoldings.FewestNets.ThreeExitGraftStrictFiber
public import Unfoldings.Roof.PotentialContourGapVertexMarks
public import Unfoldings.Complex.ContourChildGapStacks
public import Unfoldings.Metric.BankStackAdjacentGaps


/-! Original incidences between two gaps in the same child stack. -/

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

local instance graftChildPairClassesIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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
local notation "BankAt[" e "]" => PotentialCutForest.contourSourceRay Fcut S.contour S.starts e
local notation "MovedAt[" e "]" => PotentialCutForest.contourSourceOpenedRay Fcut S.contour S.starts e
local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams Left Right
/-- Two consecutive gaps in a child's stack are consecutive on both original attachments. -/
theorem contourGraftChildPair_slots
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Fcut).parents.roots)
    (parent_nonroot : (Fcut).parents.parent v ∉ (Fcut).parents.roots)
    (e f : Event) (before after : List Event)
    (consecutive : Stack FiniteBank[v,nonroot] = before ++ e :: f :: after) :
    let child := FiniteBank[v,nonroot]
    let parent := FiniteBank[(Fcut).parents.parent v,parent_nonroot]
    ∃ (i : Fin ((Stack parent).length + 1)) (j : Fin ((Stack child).length + 1)),
      Named false ⟨parent, i⟩ 0 = ⟨parent, some e, true, 0⟩ ∧
      Named true ⟨parent, i⟩ 0 = ⟨parent, some f, false, 0⟩ ∧
      Named false ⟨child, j⟩ 1 = ⟨child, some e, true, 1⟩ ∧
      Named true ⟨child, j⟩ 1 = ⟨child, some f, false, 1⟩ := by
  let child := FiniteBank[v,nonroot]
  let parent := FiniteBank[(Fcut).parents.parent v,parent_nonroot]
  obtain ⟨pre, post, block⟩ := (D).contourSavedGapStack_child_block Selection S.contour
    (Fcut).boundary_roots S.starts v nonroot
  have extend : Stack parent = pre ++ Stack child ++ post := block
  have above : Stack parent = (pre ++ before) ++ e :: f :: (after ++ post) := by
    calc
      _ = pre ++ Stack child ++ post := extend
      _ = pre ++ (before ++ e :: f :: after) ++ post :=
        congrArg (fun l => pre ++ l ++ post) consecutive
      _ = _ := by simp only [List.append_assoc, List.cons_append]
  obtain ⟨i, hi, ri⟩ := MetricGluing.bankStack_exists_adjacent_gap_slot
    (Parameter := Param) Stack parent 0 above
  obtain ⟨j, hj, rj⟩ := MetricGluing.bankStack_exists_adjacent_gap_slot
    (Parameter := Param) Stack child 1 consecutive
  exact ⟨i, j, hi, ri, hj, rj⟩

-- This isolates the dependent original address recovery from the class computation.
private theorem recover_bend_address
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Fcut).parents.roots)
    (parent_nonroot : (Fcut).parents.parent v ∉ (Fcut).parents.roots)
    (e : Event)
    (here : e ∈ Stack FiniteBank[v,nonroot])
    (above : e ∈ Stack FiniteBank[(Fcut).parents.parent v,parent_nonroot])
    (side : Bool) (a : Addr) (valid : Valid a)
    (eq : Mark a valid = ⟨some e,
      Gap FiniteBank[(Fcut).parents.parent v,parent_nonroot] e above side 0⟩) :
    a = ⟨FiniteBank[v,nonroot], some e, side, 1⟩ ∨
      a = ⟨FiniteBank[(Fcut).parents.parent v,parent_nonroot], some e, side, 0⟩ := by
  obtain ⟨b, tag, flag, t⟩ := a
  cases tag with
  | none => cases congrArg Sigma.fst eq
  | some other =>
    have match_tag : other = e := Option.some.inj
      (congrArg (fun z : MetricGluing.Total Pieces => z.1) eq)
    subst other
    have value : Gap b e valid flag t =
        Gap FiniteBank[(Fcut).parents.parent v,parent_nonroot] e above side 0 :=
      eq_of_heq (Sigma.mk.inj eq).2
    obtain ⟨flag_eq, parameter⟩ :=
      (Fcut).contourGapMark_parent_bend_address S.contour S.starts S.gaps
        v nonroot parent_nonroot e here above side b valid flag t value
    subst flag
    let tagged (x : Σ b : Attachment, Param b) : Addr := ⟨x.1, some e, side, x.2⟩
    exact parameter.imp (congrArg tagged) (congrArg tagged)

/-- The two literal endpoint names of a finite bend agree and exhaust its incident slots. -/
theorem contourGraftGapBend_endpoint_transfer
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Fcut).parents.roots)
    (parent_nonroot : (Fcut).parents.parent v ∉ (Fcut).parents.roots)
    (e : Event) (_g : OrientedBankGap BankAt[e] MovedAt[e])
    (i : Fin ((Stack FiniteBank[(Fcut).parents.parent v,parent_nonroot]).length + 1))
    (j : Fin ((Stack FiniteBank[v,nonroot]).length + 1)) (side flag : Bool)
    (first_named : Named side ⟨FiniteBank[(Fcut).parents.parent v,parent_nonroot], i⟩ 0 =
      ⟨FiniteBank[(Fcut).parents.parent v,parent_nonroot], some e, flag, 0⟩)
    (last_named : Named side ⟨FiniteBank[v,nonroot], j⟩ 1 =
      ⟨FiniteBank[v,nonroot], some e, flag, 1⟩) :
    let first : Time := ⟨⟨FiniteBank[(Fcut).parents.parent v,parent_nonroot], i⟩, 0⟩
    let second : Time := ⟨⟨FiniteBank[v,nonroot], j⟩, 1⟩
    EndAt side first.1 first.2 = EndAt side second.1 second.2 ∧
    ∀ (other : Bool) (p : Time), EndAt other p.1 p.2 = EndAt side first.1 first.2 →
      other = side ∧ (p = first ∨ p = second) := by
  let child := FiniteBank[v,nonroot]
  let parent := FiniteBank[(Fcut).parents.parent v,parent_nonroot]
  let first : Time := ⟨⟨parent, i⟩, 0⟩
  let second : Time := ⟨⟨child, j⟩, 1⟩
  have here : e ∈ Stack child := show Valid ⟨child, some e, flag, 1⟩ from
    last_named ▸ MetricGluing.bankStackEndpointAddress_valid Stack side second.1 second.2
  have above : e ∈ Stack parent := show Valid ⟨parent, some e, flag, 0⟩ from
    first_named ▸ MetricGluing.bankStackEndpointAddress_valid Stack side first.1 first.2
  have outgoing := MetricGluing.bankStackEndpoint_eq_of_gap_address
    Stack Pieces Base Gap side first parent e above flag 0 first_named
  have incoming := MetricGluing.bankStackEndpoint_eq_of_gap_address
    Stack Pieces Base Gap side second child e here flag 1 last_named
  have join := (Fcut).contourGapMark_parent_join S.contour S.starts S.gaps v nonroot parent_nonroot
    e here above flag
  refine ⟨outgoing.trans ((congrArg (Sigma.mk (some e)) join).symm.trans incoming.symm), ?_⟩
  intro other p same
  let a := Named other p.1 p.2
  let valid := MetricGluing.bankStackEndpointAddress_valid Stack other p.1 p.2
  have actual : Mark a valid = ⟨some e, Gap parent e above flag 0⟩ :=
    (MetricGluing.bankStackAddressPoint_endpoint Stack Pieces Base Gap other p.1 p.2).trans
      (same.trans outgoing)
  have named := recover_bend_address L S v nonroot parent_nonroot e here above flag
    a valid actual
  let inj := MetricGluing.bankStackEndpointAddress_injective (Parameter := Param) Stack
    (contourGraft_stack_nodup S)
  rcases named with h | h
  · have recovered : (other, p) = (side, second) := inj (h.trans last_named.symm)
    exact ⟨congrArg Prod.fst recovered, Or.inr (congrArg Prod.snd recovered)⟩
  · have recovered : (other, p) = (side, first) := inj (h.trans first_named.symm)
    exact ⟨congrArg Prod.fst recovered, Or.inl (congrArg Prod.snd recovered)⟩

set_option maxHeartbeats 180000 in
-- Membership, literal addresses and seam classes all use the original dependent attachment types.
/-- The class between consecutive gaps in the same child block has exactly those
two bend marks and their original incoming and outgoing seam slots. -/
theorem contourGraftChildPair_class
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Fcut).parents.roots)
    (parent_nonroot : (Fcut).parents.parent v ∉ (Fcut).parents.roots)
    (e f : Event) (g : OrientedBankGap BankAt[e] MovedAt[e])
    (h : OrientedBankGap BankAt[f] MovedAt[f]) (before after : List Event)
    (consecutive : Stack FiniteBank[v,nonroot] = before ++ e :: f :: after) :
    let child := FiniteBank[v,nonroot]
    let parent := FiniteBank[(Fcut).parents.parent v,parent_nonroot]
    ∃ (i : Fin ((Stack parent).length + 1)) (j : Fin ((Stack child).length + 1)),
      let first : Time := ⟨⟨parent, i⟩, 0⟩
      let second : Time := ⟨⟨child, j⟩, 1⟩
      (∀ x, Relation.EqvGen Banks (Left first.1 first.2) x ↔
        x = Left first.1 first.2 ∨ x = Right first.1 first.2) ∧
      (∀ (side other : Bool) (p : Time),
        EndAt other p.1 p.2 = EndAt side first.1 first.2 →
        other = side ∧ (p = first ∨ p = second)) ∧
      Named false first.1 first.2 = ⟨parent, some e, true, 0⟩ ∧
      Named true first.1 first.2 = ⟨parent, some f, false, 0⟩ ∧
      Named false second.1 second.2 = ⟨child, some e, true, 1⟩ ∧
      Named true second.1 second.2 = ⟨child, some f, false, 1⟩ := by
  obtain ⟨i, j, le, rf, le', rf'⟩ := contourGraftChildPair_slots S v nonroot parent_nonroot e f before after consecutive
  let first : Time := ⟨⟨FiniteBank[(Fcut).parents.parent v,parent_nonroot], i⟩, 0⟩
  let second : Time := ⟨⟨FiniteBank[v,nonroot], j⟩, 1⟩
  obtain ⟨linkL, recoverL⟩ := L.contourGraftGapBend_endpoint_transfer S v nonroot
    parent_nonroot e g i j false true le le'
  obtain ⟨linkR, recoverR⟩ := L.contourGraftGapBend_endpoint_transfer S v nonroot
    parent_nonroot f h i j true false rf rf'
  have link (side : Bool) : EndAt side first.1 first.2 = EndAt side second.1 second.2 := by
    cases side
    · exact linkL
    · exact linkR
  have recover (side other : Bool) (p : Time)
      (eq : EndAt other p.1 p.2 = EndAt side first.1 first.2) :
      other = side ∧ (p = first ∨ p = second) := by
    cases side
    · exact recoverL other p eq
    · exact recoverR other p eq
  exact ⟨i, j, MetricGluing.bankStack_eqvGen_pair_of_two_slot_times Stack Pieces Base Gap
    first second link recover, recover, le, rf, le', rf'⟩

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
