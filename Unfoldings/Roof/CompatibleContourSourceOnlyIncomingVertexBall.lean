module

public import Unfoldings.Roof.CompatibleContourSourceOnlyOutgoingVertexBall
public import Unfoldings.Roof.CompatibleContourSourceOnlySmoothSeams
public import Unfoldings.Roof.CompatibleContourSourceOnlyTerminalJoinBall

/-! Incoming finite banks transfer their planar charts across the actual bend or terminal join. -/

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

local instance sourceOnlyIncomingVertexBallIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlyIncomingVertexBallWholeFintype : Fintype W.Index := W.finiteIndex

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

local notation "Point" => MetricGluing.point Pieces Banks
local notation "LengthAt[" e "]" => TriangleComplex.positiveContourBankLength D Selection contour e
local notation "Terminal" => TriangleComplex.ContourTerminalEdge D Selection

omit beta acute in
private theorem point_endpoint_eq_left {G B : Type*} {Parameter : B → Type*}
    (X : Option G → Type*) [∀ i, PseudoEMetricSpace (X i)] (stack : B → List G)
    (base : ∀ e, Bool → Parameter e → X none)
    (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))
    (side : Bool) (slot : MetricGluing.BankStackSlot stack) (t : Parameter slot.1) :
    let left :=  MetricGluing.bankStackLeft X stack base gap
    let right := MetricGluing.bankStackRight X stack base gap
    MetricGluing.point X (MetricGluing.bankSeams left right)
      (MetricGluing.bankStackEndpoint stack X base gap side slot t) =
      MetricGluing.point X (MetricGluing.bankSeams left right) (left slot t) := by
  cases side
  · rfl
  · exact (MetricGluing.point_eq_of_glue X ⟨slot, t, rfl, rfl⟩).symm

private theorem exists_compatibleContourSourceOnlyGapMark_endpoint
    (bank : Attachment) (e : Event) (mem : e ∈ Stack bank) (flag : Bool) (t : ParamAt bank) :
    ∃ i : Fin ((Stack bank).length + 1), ∃ side : Bool,
      EndAt side ⟨bank, i⟩ t = ⟨some e, Gap bank e mem flag t⟩ := by
  obtain ⟨j, name⟩ := List.get_of_mem mem
  cases flag
  · refine ⟨j.castSucc, true, ?_⟩
    have right : Rgt ⟨bank, j.castSucc⟩ t =
        ⟨some ((Stack bank).get j), Gap bank ((Stack bank).get j)
          (List.get_mem (Stack bank) j) false t⟩ :=
      MetricGluing.bankStackRight_at Pieces Stack Base Gap bank j t
    change Rgt ⟨bank, j.castSucc⟩ t = _
    rw [right]
    exact Eq.mp (congrArg (fun g : Event => ∀ hm : g ∈ Stack bank,
      (⟨some ((Stack bank).get j), Gap bank ((Stack bank).get j)
        (List.get_mem (Stack bank) j) false t⟩ : MetricGluing.Total Pieces) =
        ⟨some g, Gap bank g hm false t⟩) name) (fun _ => rfl) mem
  · refine ⟨j.succ, false, ?_⟩
    have left : L ⟨bank, j.succ⟩ t =
        ⟨some ((Stack bank).get j), Gap bank ((Stack bank).get j)
          (List.get_mem (Stack bank) j) true t⟩ :=
      MetricGluing.bankStackLeft_after Pieces Stack Base Gap bank j t
    change L ⟨bank, j.succ⟩ t = _
    rw [left]
    exact Eq.mp (congrArg (fun g : Event => ∀ hm : g ∈ Stack bank,
      (⟨some ((Stack bank).get j), Gap bank ((Stack bank).get j)
        (List.get_mem (Stack bank) j) true t⟩ : MetricGluing.Total Pieces) =
        ⟨some g, Gap bank g hm true t⟩) name) (fun _ => rfl) mem

/-- Every slot at the end of a terminal finite attachment has the tail's whole planar ball. -/
theorem compatibleContourSourceOnlyTerminalFinite_planarBall
    (edge : Terminal) (i : Fin ((Stack (.inr edge)).length + 1)) :
    HasMetricBallChart ℂ (Point (L ⟨FiniteBank[edge.val,edge.property.1], i⟩ 1)) := by
  have first := K.compatibleContourSourceOnlyJoinedBank_finite compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W geometry edge i false 1
  have second := K.compatibleContourSourceOnlyJoinedBank_tail compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W geometry edge i false 0
  have same_time : bankJoinFiniteTime 1 = bankJoinTailTime 0 := by
    apply Subtype.ext
    exact sub_self (1 : ℝ)
  rw [same_time] at first
  have same : L ⟨FiniteBank[edge.val,edge.property.1], i⟩ 1 = L ⟨.inr edge, i⟩ 0 :=
    first.symm.trans second
  exact Eq.mpr (congrArg (fun z : MetricGluing.Total Pieces => HasMetricBallChart ℂ (Point z)) same)
    (K.compatibleContourSourceOnlyTerminalJoin_planarBall compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W geometry edge i)

set_option maxHeartbeats 1600000 in
-- The original lower and upper attachments carry dependent stack index types.
/-- At a nonterminal incoming bank with a gap, each end slot reaches the parent
through that gap's literal bend. The whole chart comes from the outgoing bank. -/
theorem compatibleContourSourceOnlyFiniteEnd_nonempty_planarBall
    (ends : (D).contourOriginalVertex Selection contour (Fin.last contour.length) ∈
      (Fcut).parents.roots)
    (child : Edge) (hp : (Fcut).parents.parent child.val ∉ (Fcut).parents.roots)
    (nonempty_stack : Stack FiniteBank[child.val,child.property] ≠ [])
    (strict : ∀ (e : Event) (k : Fin LengthAt[e]), let B := BankAt[e]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ))
    (i : Fin ((Stack FiniteBank[child.val,child.property]).length + 1)) :
    HasMetricBallChart ℂ (Point (L ⟨FiniteBank[child.val,child.property], i⟩ 1)) := by
  let parent : Edge := ⟨(Fcut).parents.parent child.val, hp⟩
  let b := FiniteBank[child.val,child.property]
  let p := FiniteBank[parent.val,parent.property]
  have pick : ∃ (e : Event) (h : e ∈ Stack b) (side flag : Bool),
      EndAt side ⟨b, i⟩ 1 = ⟨some e, Gap b e h flag 1⟩ := by
    by_cases zero : i.val = 0
    · have i0 : i = 0 := Fin.ext zero
      let j : Fin (Stack b).length := ⟨0, List.length_pos_iff.mpr nonempty_stack⟩
      refine ⟨(Stack b).get j, List.get_mem _ j, true, false, ?_⟩
      rw [i0]
      exact MetricGluing.bankStackRight_at Pieces Stack Base Gap b j 1
    · have bound : i.val < (Stack b).length + 1 := i.isLt
      let j : Fin (Stack b).length := ⟨i.val - 1, by omega⟩
      have label : j.succ = i := Fin.ext (by change i.val - 1 + 1 = i.val; omega)
      refine ⟨(Stack b).get j, List.get_mem _ j, false, true, ?_⟩
      rw [← label]
      exact MetricGluing.bankStackLeft_after Pieces Stack Base Gap b j 1
  obtain ⟨e, at_child, side, flag, eq_child⟩ := pick
  have child_path := ((D).mem_contourSavedGapStack Selection contour child.val e).mp at_child
  have at_parent : e ∈ Stack p :=
    ((D).mem_contourSavedGapStack Selection contour parent.val e).mpr
      (child_path.trans (Fcut).parents ((Fcut).parents.ancestor_parent child.val))
  have bend := K.compatibleContourSourceOnlyGapMark_parent_join compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts models child.val child.property hp
    e at_child at_parent flag
  obtain ⟨j, other_side, eq_parent⟩ :=
    K.exists_compatibleContourSourceOnlyGapMark_endpoint compact nonempty R no_boundary level higher
      M positive inner_disk beta acute contour starts W geometry p e at_parent flag 0
  have same : EndAt side ⟨b, i⟩ 1 = EndAt other_side ⟨p, j⟩ 0 :=
    eq_child.trans ((congrArg (Sigma.mk (some e)) bend).trans eq_parent.symm)
  have label : Point (L ⟨b, i⟩ 1) = Point (EndAt true ⟨p, j⟩ 0) :=
    (point_endpoint_eq_left Pieces Stack Base Gap side ⟨b, i⟩ 1).symm.trans
      ((congrArg Point same).trans
        ((point_endpoint_eq_left Pieces Stack Base Gap other_side ⟨p, j⟩ 0).trans
          (point_endpoint_eq_left Pieces Stack Base Gap true ⟨p, j⟩ 0).symm))
  exact Eq.mpr (congrArg (HasMetricBallChart ℂ) label)
    (K.compatibleContourSourceOnly_outgoingVertex_planarBall compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W geometry ends parent strict j)

end Unfoldings.ConvexRoof
