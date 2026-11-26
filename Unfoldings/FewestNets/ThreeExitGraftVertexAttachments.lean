module

public import Unfoldings.FewestNets.ThreeExitGraftRoofRun
public import Unfoldings.FewestNets.ThreeExitGraftTerminalJoinClasses
public import Unfoldings.Roof.PotentialContourGapVertexMarks
public import Unfoldings.Metric.BankStackEndpointExistence




/-! Every incoming finite endpoint and retained roof copy reaches an exact outgoing slot. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel

open MetricGluing

universe u v

set_option maxHeartbeats 2800000

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

local instance graftVertexAttachmentsIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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

local notation "Edge" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "FiniteBank[" v "," h "]" => (Sum.inl (Subtype.mk v h) : Attachment)
local notation "Retain" => PotentialCutForest.retain Fcut
local notation "Map" => L.fineMeshWholeMap S.higher
local notation "RoofPoint[" j "]" => (Sigma.mk none (Map
  (TriangleComplex.vertexPoint D Retain (TriangleComplex.boundaryEndVertex D Retain
    (PairedInvolutions.System.Chain.point (TriangleComplex.BoundaryContour.cycle S.contour) j)))) :
      MetricGluing.Total Pieces)
local notation "Interval[" v "," h "]" => TriangleComplex.contourParentInterval
  D Selection S.contour (PotentialCutForest.boundary_roots Fcut) S.starts v h
local notation "RoofTime" => MetricGluing.bankStackRoofTime (Parameter := Param) Stack
local notation "Germ" => contourFiniteRoofGerm S
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
local notation "Point" => MetricGluing.point Pieces Banks
local notation "geometry" => S.gaps

local notation "Visit[" j "]" => TriangleComplex.contourOriginalVertex D Selection S.contour j
local notation "SiteTime" => contourGraftRoofSiteTime S

private theorem point_endpoint_eq_left {GapTag Bank : Type*} {Parameter : Bank → Type*}
    (X : Option GapTag → Type*) [∀ i, PseudoEMetricSpace (X i)] (stack : Bank → List GapTag)
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

private theorem exists_contourGraftGapMark_endpoint
    (bank : Attachment) (e : Event) (mem : e ∈ Stack bank) (flag : Bool) (t : Param bank) :
    ∃ i : Fin ((Stack bank).length + 1), ∃ side : Bool,
      EndAt side ⟨bank, i⟩ t = ⟨some e, Gap bank e mem flag t⟩ := by
  obtain ⟨j, name⟩ := List.get_of_mem mem
  cases flag
  · refine ⟨j.castSucc, true, ?_⟩
    have right : Right ⟨bank, j.castSucc⟩ t =
        ⟨some ((Stack bank).get j), Gap bank ((Stack bank).get j)
          (List.get_mem (Stack bank) j) false t⟩ :=
      MetricGluing.bankStackRight_at Pieces Stack Base Gap bank j t
    change Right ⟨bank, j.castSucc⟩ t = _
    rw [right]
    exact Eq.mp (congrArg (fun g : Event => ∀ hm : g ∈ Stack bank,
      (⟨some ((Stack bank).get j), Gap bank ((Stack bank).get j)
        (List.get_mem (Stack bank) j) false t⟩ : MetricGluing.Total Pieces) =
        ⟨some g, Gap bank g hm false t⟩) name) (fun _ => rfl) mem
  · refine ⟨j.succ, false, ?_⟩
    have left : Left ⟨bank, j.succ⟩ t =
        ⟨some ((Stack bank).get j), Gap bank ((Stack bank).get j)
          (List.get_mem (Stack bank) j) true t⟩ :=
      MetricGluing.bankStackLeft_after Pieces Stack Base Gap bank j t
    change Left ⟨bank, j.succ⟩ t = _
    rw [left]
    exact Eq.mp (congrArg (fun g : Event => ∀ hm : g ∈ Stack bank,
      (⟨some ((Stack bank).get j), Gap bank ((Stack bank).get j)
        (List.get_mem (Stack bank) j) true t⟩ : MetricGluing.Total Pieces) =
        ⟨some g, Gap bank g hm true t⟩) name) (fun _ => rfl) mem

/-- At a nonterminal incoming bank with a gap, each end slot reaches a named
outgoing slot through that gap's literal bend. -/
theorem contourGraftFiniteEnd_nonempty_eq_outgoing
    (child : Edge) (hp : (Fcut).parents.parent child.val ∉ (Fcut).parents.roots)
    (nonempty_stack : Stack FiniteBank[child.val,child.property] ≠ [])
    (i : Fin ((Stack FiniteBank[child.val,child.property]).length + 1)) :
    let b := FiniteBank[(Fcut).parents.parent child.val,hp]
    ∃ j : Fin ((Stack b).length + 1),
      Point (Left ⟨FiniteBank[child.val,child.property], i⟩ 1) = Point (EndAt true ⟨b, j⟩ 0) := by
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
  have child_path := ((D).mem_contourSavedGapStack Selection S.contour child.val e).mp at_child
  have at_parent : e ∈ Stack p :=
    ((D).mem_contourSavedGapStack Selection S.contour parent.val e).mpr
      (child_path.trans (Fcut).parents ((Fcut).parents.ancestor_parent child.val))
  have bend := (Fcut).contourGapMark_parent_join S.contour S.starts S.gaps child.val child.property hp
    e at_child at_parent flag
  obtain ⟨j, other_side, eq_parent⟩ :=
    exists_contourGraftGapMark_endpoint L S p e at_parent flag 0
  have same : EndAt side ⟨b, i⟩ 1 = EndAt other_side ⟨p, j⟩ 0 :=
    eq_child.trans ((congrArg (Sigma.mk (some e)) bend).trans eq_parent.symm)
  have label : Point (Left ⟨b, i⟩ 1) = Point (EndAt true ⟨p, j⟩ 0) :=
    (point_endpoint_eq_left Pieces Stack Base Gap side ⟨b, i⟩ 1).symm.trans
      ((congrArg Point same).trans
        ((point_endpoint_eq_left Pieces Stack Base Gap other_side ⟨p, j⟩ 0).trans
          (point_endpoint_eq_left Pieces Stack Base Gap true ⟨p, j⟩ 0).symm))
  exact ⟨j, label⟩

/-- Every original roof copy at a nonroot vertex reaches a named outgoing slot.
Empty children restore their seams and nonempty children reach it through a gap. -/
theorem contourGraftRoofVertex_eq_outgoing
    (j : Fin (S.contour.length + 1)) (nonroot : Visit[j] ∉ (Fcut).parents.roots) :
    let b := FiniteBank[Visit[j],nonroot]
    ∃ k : Fin ((Stack b).length + 1), Point RoofPoint[j] = Point (EndAt true ⟨b, k⟩ 0) := by
  let parent : Edge := ⟨Visit[j], nonroot⟩
  let A := (D).contourFullParentWedgeRun Selection S.contour (Fcut).boundary_roots S.starts parent
  let b := FiniteBank[parent.val,parent.property]
  let data := Interval[parent.val,parent.property]
  have bounds := (data.subtree j).mp ((Fcut).parents.ancestor_refl parent.val)
  have offset := (D).contourParentInterval_enter_succ_val Selection S.contour (Fcut).boundary_roots
    S.starts parent.val parent.property
  have above_first : finRotate (S.contour.length + 1) data.enter ≤ j := by
    change (finRotate (S.contour.length + 1) data.enter).val ≤ j.val
    change data.enter.val < j.val ∧ j.val ≤ data.leave.val at bounds
    change (finRotate (S.contour.length + 1) data.enter).val = data.enter.val + 1 at offset
    omega
  obtain ⟨v, at_j⟩ := (A.visits j).mpr ⟨rfl, above_first, bounds.2⟩
  have first_germ : Germ parent true false =
      (D).boundaryMate Retain (S.contour.cycle.point (A.visit 0)) :=
    ((D).contourParent_firstVisit_germ Selection S.contour (Fcut).boundary_roots S.starts
      parent.val parent.property).symm.trans
      (congrArg (fun i => (D).boundaryMate Retain (S.contour.cycle.point i)) A.at_first.symm)
  have last_germ : Germ parent false false = S.contour.cycle.point (A.visit (Fin.last A.length)) :=
    ((D).contourParent_lastVisit_germ Selection S.contour (Fcut).boundary_roots S.starts
      parent.val parent.property).symm.trans (congrArg S.contour.cycle.point A.at_last.symm)
  obtain ⟨_, endpoints⟩ := L.contourGraftRoofRun_endpoints S parent A
    (parent, true, false) (parent, false, false) first_germ last_germ
  let outgoing (z : MetricGluing.Realization Pieces Banks) : Prop :=
    ∃ k : Fin ((Stack b).length + 1), z = Point (EndAt true ⟨b, k⟩ 0)
  have every (i : Fin (A.length + 1)) : outgoing (Point RoofPoint[A.visit i]) := by
    induction i using Fin.inductionOn with
    | zero =>
      let s : Time := ⟨⟨b, Fin.last (Stack b).length⟩, 0⟩
      have label : EndAt true s.1 s.2 = RoofPoint[A.visit 0] :=
        (endpoints 0 true s).mpr (Or.inl ⟨rfl, rfl⟩)
      exact ⟨Fin.last (Stack b).length, congrArg Point label.symm⟩
    | succ i ih =>
      let child := A.child i
      let a := FiniteBank[child.val,child.property]
      let s : Time := ⟨⟨a, 0⟩, 1⟩
      have label : Left s.1 s.2 = RoofPoint[A.visit i.succ] := by
        apply (endpoints i.succ false s).mpr
        refine Or.inl ⟨rfl, ?_⟩
        change s = ⟨⟨a, 0⟩, unitInterval.symm 0⟩
        rw [unitInterval.symm_zero]
      have held : outgoing (Point (Left s.1 s.2)) := by
        by_cases empty : Stack a = []
        · have same_slot : Fin.last (Stack a).length = 0 := by
            apply Fin.ext
            change (Stack a).length = 0
            rw [empty]
            rfl
          let q := contourGraftRoofRunOutgoing S A (parent, false, false)
          have prior_site : q i.castSucc = (child, true, true) := by
            change Fin.lastCases (motive := fun _ => Edge × Bool × Bool)
              (parent, false, false) (fun j => (A.child j, true, true)) i.castSucc = _
            exact Fin.lastCases_castSucc i
          have prev_label : Right s.1 s.2 = RoofPoint[A.visit i.castSucc] := by
            apply (endpoints i.castSucc true s).mpr
            right
            change true = (q i.castSucc).2.1 ∧ s = SiteTime (q i.castSucc)
            rw [prior_site]
            refine ⟨rfl, ?_⟩
            change s = ⟨⟨a, Fin.last (Stack a).length⟩, unitInterval.symm 0⟩
            rw [same_slot, unitInterval.symm_zero]
          have glued : Point (Left s.1 s.2) = Point (Right s.1 s.2) :=
            MetricGluing.point_eq_of_glue Pieces (glue := Banks) ⟨s.1, s.2, rfl, rfl⟩
          obtain ⟨k, h⟩ := ih
          exact ⟨k, glued.trans ((congrArg Point prev_label).trans h)⟩
        · have hp : (Fcut).parents.parent child.val ∉ (Fcut).parents.roots :=
            (A.child_parent i).symm ▸ nonroot
          obtain ⟨k, witness⟩ := L.contourGraftFiniteEnd_nonempty_eq_outgoing S child hp empty 0
          let atParent (p : Edge) : Prop :=
            let a := FiniteBank[p.val,p.property]
            ∃ k : Fin ((Stack a).length + 1), Point (Left s.1 s.2) = Point (EndAt true ⟨a, k⟩ 0)
          have with_child : atParent ⟨(Fcut).parents.parent child.val, hp⟩ := ⟨k, witness⟩
          have same : (⟨(Fcut).parents.parent child.val, hp⟩ : Edge) = parent :=
            Subtype.ext (A.child_parent i)
          exact Eq.mp (congrArg atParent same) with_child
      obtain ⟨k, h⟩ := held
      exact ⟨k, (congrArg Point label).symm.trans h⟩
  exact Eq.mp (congrArg (fun i => outgoing (Point RoofPoint[i])) at_j) (every v)

/-- The restored end of an empty child stack lies at an outgoing slot of its parent. -/
theorem contourGraftFiniteEnd_empty_eq_outgoing
    (child : Edge) (hp : (Fcut).parents.parent child.val ∉ (Fcut).parents.roots)
    (empty : Stack FiniteBank[child.val,child.property] = [])
    (i : Fin ((Stack FiniteBank[child.val,child.property]).length + 1)) :
    let b := FiniteBank[(Fcut).parents.parent child.val,hp]
    ∃ k : Fin ((Stack b).length + 1),
      Point (Left ⟨FiniteBank[child.val,child.property], i⟩ 1) = Point (EndAt true ⟨b, k⟩ 0) := by
  let a := FiniteBank[child.val,child.property]
  let data := Interval[child.val,child.property]
  have at_parent : Visit[data.enter] = (Fcut).parents.parent child.val :=
    ((D).contourParentInterval_entry_original Selection S.contour (Fcut).boundary_roots S.starts
      child.val child.property).1
  have i0 : i = 0 := by
    apply Fin.ext
    have bound : i.val < (Stack a).length + 1 := i.isLt
    have len : (Stack a).length = 0 := congrArg List.length empty
    change i.val = 0
    omega
  have roof_mark : Base a true 1 = (RoofPoint[data.enter]).2 := by
    have mark := L.contourFiniteRoofGerm_mark S child true true 0
    have turn : Germ child true true = S.contour.cycle.point data.enter :=
      (D).boundaryTurn_involutive Retain _
    change Base a true (unitInterval.symm 0) =
      Map ((D).directedBoundaryPath (Germ child true true) 0) at mark
    rw [unitInterval.symm_zero, turn] at mark
    exact mark.trans (congrArg Map ((D).directedBoundaryPath_zero (S.contour.cycle.point data.enter)))
  have mark := MetricGluing.bankStackEndpoint_eq_of_base_address Stack Pieces Base Gap true
    (⟨⟨a, 0⟩, 1⟩ : Time) a true 1
    (MetricGluing.bankStack_empty_addresses (Parameter := Param) Stack a 1 empty).2
  have same : Point (Left ⟨a, 0⟩ 1) = Point RoofPoint[data.enter] := by
    have glue : Point (Left ⟨a, 0⟩ 1) = Point (Right ⟨a, 0⟩ 1) :=
      MetricGluing.point_eq_of_glue Pieces (glue := Banks) ⟨⟨a, 0⟩, 1, rfl, rfl⟩
    exact glue.trans (congrArg Point (mark.trans (congrArg (Sigma.mk none) roof_mark)))
  obtain ⟨k, hk⟩ := L.contourGraftRoofVertex_eq_outgoing S data.enter
    (at_parent.symm ▸ hp)
  let P (v : Edge) := ∃ k : Fin ((Stack (.inl v)).length + 1),
    Point (Left ⟨a, i⟩ 1) = Point (EndAt true ⟨.inl v, k⟩ 0)
  have at_visit : P ⟨Visit[data.enter], at_parent.symm ▸ hp⟩ := by
    refine ⟨k, ?_⟩
    rw [i0]
    exact same.trans hk
  exact Eq.mp (congrArg P (Subtype.ext at_parent)) at_visit

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
