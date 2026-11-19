module

public import Unfoldings.Complex.ContourChildGapStacks
public import Unfoldings.Metric.BankStackAdjacentGaps
public import Unfoldings.Roof.CompatibleContourSourceOnlyGapVertexMarks
public import Unfoldings.Roof.CompatibleContourFiniteSeamClasses

/-! Exact seam classes between two consecutive gaps within the same incoming child block. -/

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

local instance sourceOnlySameChildIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlySameChildWholeFintype : Fintype W.Index := W.finiteIndex

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

include starts in
/-- Two consecutive gaps in a child's stack are consecutive on both original attachments. -/
theorem compatibleContourSourceOnlyChildPair_slots
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
  obtain ⟨pre, post, block⟩ := (D).contourSavedGapStack_child_block Selection contour
    (Fcut).boundary_roots starts v nonroot
  have extend : Stack parent = pre ++ Stack child ++ post := block
  have above : Stack parent = (pre ++ before) ++ e :: f :: (after ++ post) := by
    calc
      _ = pre ++ Stack child ++ post := extend
      _ = pre ++ (before ++ e :: f :: after) ++ post :=
        congrArg (fun l => pre ++ l ++ post) consecutive
      _ = _ := by simp only [List.append_assoc, List.cons_append]
  obtain ⟨i, hi, ri⟩ := MetricGluing.bankStack_exists_adjacent_gap_slot
    (Parameter := ParamAt) Stack parent 0 above
  obtain ⟨j, hj, rj⟩ := MetricGluing.bankStack_exists_adjacent_gap_slot
    (Parameter := ParamAt) Stack child 1 consecutive
  exact ⟨i, j, hi, ri, hj, rj⟩

-- This isolates the dependent original address recovery from the class computation.
private theorem recover_bend_address
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Fcut).parents.roots)
    (parent_nonroot : (Fcut).parents.parent v ∉ (Fcut).parents.roots)
    (e : Event) (g : OrientedBankGap BankAt[e] MovedAt[e])
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
      K.compatibleContourSourceOnlyGapMark_parent_bend_address compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts models
        v nonroot parent_nonroot e g here above side b valid flag t value
    subst flag
    let tagged (x : Σ b : Attachment, ParamAt b) : Addr := ⟨x.1, some e, side, x.2⟩
    exact parameter.imp (congrArg tagged) (congrArg tagged)

/-- The two literal endpoint names of a finite bend agree and exhaust its incident slots. -/
theorem compatibleContourSourceOnlyGapBend_endpoint_transfer
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Fcut).parents.roots)
    (parent_nonroot : (Fcut).parents.parent v ∉ (Fcut).parents.roots)
    (e : Event) (g : OrientedBankGap BankAt[e] MovedAt[e])
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
  have join := K.compatibleContourSourceOnlyGapMark_parent_join compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts models v nonroot parent_nonroot
    e here above flag
  refine ⟨outgoing.trans ((congrArg (Sigma.mk (some e)) join).symm.trans incoming.symm), ?_⟩
  intro other p same
  let a := Named other p.1 p.2
  let valid := MetricGluing.bankStackEndpointAddress_valid Stack other p.1 p.2
  have actual : Mark a valid = ⟨some e, Gap parent e above flag 0⟩ :=
    (MetricGluing.bankStackAddressPoint_endpoint Stack Pieces Base Gap other p.1 p.2).trans
      (same.trans outgoing)
  have named := recover_bend_address K compact nonempty R no_boundary level higher M positive
    inner_disk beta acute contour starts W models v nonroot parent_nonroot e g here above flag
    a valid actual
  let inj := MetricGluing.bankStackEndpointAddress_injective (Parameter := ParamAt) Stack
    (K.compatibleContourBankStack_nodup compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour)
  rcases named with h | h
  · have recovered : (other, p) = (side, second) := inj (h.trans last_named.symm)
    exact ⟨congrArg Prod.fst recovered, Or.inr (congrArg Prod.snd recovered)⟩
  · have recovered : (other, p) = (side, first) := inj (h.trans first_named.symm)
    exact ⟨congrArg Prod.fst recovered, Or.inl (congrArg Prod.snd recovered)⟩

set_option maxHeartbeats 180000 in
-- Membership, literal addresses and seam classes all use the original dependent attachment types.
/-- The class between consecutive gaps in the same child block has exactly those
two bend marks and their original incoming and outgoing seam slots. -/
theorem compatibleContourSourceOnlyChildPair_class
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
      (∀ x, Relation.EqvGen Banks (L first.1 first.2) x ↔
        x = L first.1 first.2 ∨ x = Rgt first.1 first.2) ∧
      (∀ (side other : Bool) (p : Time),
        EndAt other p.1 p.2 = EndAt side first.1 first.2 →
        other = side ∧ (p = first ∨ p = second)) ∧
      Named false first.1 first.2 = ⟨parent, some e, true, 0⟩ ∧
      Named true first.1 first.2 = ⟨parent, some f, false, 0⟩ ∧
      Named false second.1 second.2 = ⟨child, some e, true, 1⟩ ∧
      Named true second.1 second.2 = ⟨child, some f, false, 1⟩ := by
  obtain ⟨i, j, le, rf, le', rf'⟩ := K.compatibleContourSourceOnlyChildPair_slots
    compact nonempty R no_boundary level higher M positive inner_disk beta acute contour
    starts v nonroot parent_nonroot e f before after consecutive
  let first : Time := ⟨⟨FiniteBank[(Fcut).parents.parent v,parent_nonroot], i⟩, 0⟩
  let second : Time := ⟨⟨FiniteBank[v,nonroot], j⟩, 1⟩
  obtain ⟨linkL, recoverL⟩ := compatibleContourSourceOnlyGapBend_endpoint_transfer K compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models v nonroot
    parent_nonroot e g i j false true le le'
  obtain ⟨linkR, recoverR⟩ := compatibleContourSourceOnlyGapBend_endpoint_transfer K compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models v nonroot
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

end Unfoldings.ConvexRoof
