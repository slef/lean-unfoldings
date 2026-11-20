module

public import Unfoldings.Roof.CompatibleContourSourceOnlyCrossBlockClasses
public import Unfoldings.Roof.CompatibleContourFiniteRoofEndpoints
public import Unfoldings.Complex.ContourExtremeChildWedgeRun
public import Unfoldings.Metric.BankStackSingleBendCycle
public import Unfoldings.Metric.BankStackRoofEndpoints

/-! The first child gap bend and the leading roof wedges form the entry-side class. -/

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

local instance sourceOnlyFirstChildIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlyFirstChildWholeFintype : Fintype W.Index := W.finiteIndex

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



local notation "Germ" => K.compatibleContourFiniteRoofGerm compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts
local notation "RoofTime" => MetricGluing.bankStackRoofTime (Parameter := ParamAt) Stack

set_option maxHeartbeats 2300000 in
-- The leading run and the oldest gap use exact dependent endpoint addresses.
/-- When the oldest outgoing gap comes from a child, its bend and the leading
roof wedges form the entire class at the parent's outgoing entry bank. -/
theorem exists_compatibleContourSourceOnlyFirstChildClass
    (parent child : Edge) (at_parent : (Fcut).parents.parent child.val = parent.val)
    (event : Event) (in_child : (Fcut).parents.Ancestor SourceOf[event] child.val)
    (g : OrientedBankGap BankAt[event] MovedAt[event])
    (later : List Event) (last_event : Stack FiniteBank[parent.val,parent.property] = later ++ [event]) :
    let first := finRotate (contour.length + 1) (Interval[parent.val,parent.property]).enter
    let last := (Interval[child.val,child.property]).enter
    let a := FiniteBank[child.val,child.property]
    let b := FiniteBank[parent.val,parent.property]
    let opening := RoofTime b true 0
    let closing := RoofTime a true 1
    ∃ (A : (D).ContourParentWedgeRun Selection contour (Fcut).boundary_roots starts
      parent.val first last)
      (H : MetricGluing.BankStackCyclicClass Pieces Stack Base Gap (A.length + 1)),
      H.center 0 = EndAt false opening.1 opening.2 ∧
      (∀ i : Fin (A.length + 1), H.center i.succ = RoofPoint[A.visit i]) ∧
      H.time = MetricGluing.BankStackCyclicClass.singleTime opening closing
        (fun i => ⟨⟨FiniteBank[(A.child i).val,(A.child i).property], 0⟩, 1⟩) ∧
      H.side = MetricGluing.BankStackCyclicClass.singleSideWith false true ∧
      (∀ i, Stack FiniteBank[(A.child i).val,(A.child i).property] = []) ∧
      (∃ after, Stack a = after ++ [event]) ∧ Function.Injective H.center := by
  let a := FiniteBank[child.val,child.property]
  let b := FiniteBank[parent.val,parent.property]
  let opening := RoofTime b true 0
  let closing := RoofTime a true 1
  let bend := EndAt false opening.1 opening.2
  have oldest (e : Event) (member : e ∈ Stack b) : event.val.val ≤ e.val.val := by
    have sorted : (Stack b).Pairwise (fun a b => b.val.val < a.val.val) :=
      ((D).contourEdgeGapStack_ordered Selection contour parent.val).reverse
    rw [last_event] at sorted member
    rcases List.mem_append.mp member with in_before | at_last
    · exact ((List.pairwise_append.mp sorted).2.2 e in_before event List.mem_cons_self).le
    · have eq := List.mem_singleton.mp at_last
      exact eq.symm ▸ le_rfl
  have at_child : event ∈ Stack a :=
    ((D).mem_contourSavedGapStack Selection contour child.val event).mpr in_child
  have oldest_child (e : Event) (member : e ∈ Stack a) : event.val.val ≤ e.val.val :=
    oldest e (((D).mem_contourSavedGapStack Selection contour parent.val e).mpr
      ((((D).mem_contourSavedGapStack Selection contour child.val e).mp member).trans (Fcut).parents
        (at_parent ▸ (Fcut).parents.ancestor_parent child.val)))
  obtain ⟨before, after, child_eq⟩ := List.append_of_mem at_child
  have no_later : after = [] := by
    by_contra! present
    obtain ⟨e, member⟩ := List.exists_mem_of_ne_nil after present
    have sorted : (Stack a).Pairwise (fun a b => b.val.val < a.val.val) :=
      ((D).contourEdgeGapStack_ordered Selection contour child.val).reverse
    have out := (List.pairwise_cons.mp (List.pairwise_append.mp (child_eq ▸ sorted)).2.1).1
      e member
    exact (not_lt_of_ge (oldest_child e
      (child_eq.symm ▸ List.mem_append_right before (List.mem_cons_of_mem event member)))) out
  have child_end : Stack a = before ++ [event] := by simpa only [no_later] using child_eq
  obtain ⟨A, empty⟩ := (D).exists_contourFirstChildWedgeRun Selection contour (Fcut).boundary_roots
    starts parent child at_parent event in_child (fun e member _ => oldest e member)
  let roof (i : Fin (A.length + 1)) := RoofPoint[A.visit i]
  let bank (e : Edge) := FiniteBank[e.val,e.property]
  let time (i : Fin A.length) : Time := ⟨⟨bank (A.child i), 0⟩, 1⟩
  have open_name := MetricGluing.bankStack_last_gap_addresses (Parameter := ParamAt)
    Stack b 0 event later last_event
  have close_name := MetricGluing.bankStack_last_gap_addresses (Parameter := ParamAt)
    Stack a 1 event before child_end
  have bend_transfer : EndAt false opening.1 opening.2 = EndAt false closing.1 closing.2 ∧
      ∀ (flag : Bool) (s : Time), EndAt flag s.1 s.2 = bend →
        flag = false ∧ (s = opening ∨ s = closing) := by
    obtain ⟨v, nonroot⟩ := parent
    change (Fcut).parents.parent child.val = v at at_parent
    subst v
    exact K.compatibleContourSourceOnlyGapBend_endpoint_transfer compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W models child.val child.property
      nonroot event g (Fin.last (Stack b).length) (Fin.last (Stack a).length)
      false true open_name.1 close_name.1

  let preceding (i : Fin (A.length + 1)) : Edge × Bool × Bool :=
    Fin.cases (parent, true, false) (fun k => (A.child k, false, true)) i
  let prevTime (i : Fin (A.length + 1)) : Time := Fin.cases opening time i
  let nextTime (i : Fin (A.length + 1)) : Time := Fin.lastCases closing time i
  let next := A.following child
  have prev_spec (i : Fin (A.length + 1)) :
      let q := preceding i
      Germ q.1 q.2.1 q.2.2 = (D).boundaryMate Retain (contour.cycle.point (A.visit i)) ∧
      RoofTime (bank q.1) q.2.1 (finiteSlotParameterize q.2.2 0) = prevTime i := by
    refine Fin.cases ?_ (fun k => ?_) i
    · change Germ parent true false = (D).boundaryMate Retain (contour.cycle.point (A.visit 0)) ∧ _
      rw [A.at_first]
      exact ⟨((D).contourParent_firstVisit_germ Selection contour (Fcut).boundary_roots
        starts parent.val parent.property).symm, rfl⟩
    · let e := A.child k
      have step := (contour.next_cyclic (D) (Interval[e.val,e.property]).leave).trans
        (congrArg contour.cycle.point (A.returns k))
      have starts_at : Germ e false true = (D).boundaryMate Retain (contour.cycle.point (A.visit k.succ)) :=
        ((D).boundaryMate_involutive Retain _).symm.trans (congrArg ((D).boundaryMate Retain) step)
      refine ⟨starts_at, ?_⟩
      change RoofTime (bank e) false (unitInterval.symm 0) = time k
      rw [unitInterval.symm_zero]
      rfl
  have next_germ (i : Fin (A.length + 1)) : Germ (next i) true true =
      contour.cycle.point (A.visit i) := by
    have target := A.following_enters child rfl i
    change (D).boundaryTurn Retain ((D).boundaryTurn Retain
      (contour.cycle.point (Interval[(next i).val,(next i).property]).enter)) = _
    exact ((D).boundaryTurn_involutive Retain _).trans (congrArg contour.cycle.point target)
  have next_spec (i : Fin (A.length + 1)) : RoofTime (bank (next i)) true 1 = nextTime i := by
    refine Fin.lastCases ?_ (fun k => ?_) i
    · change RoofTime (bank (A.following child (Fin.last A.length))) true 1 =
        Fin.lastCases (motive := fun _ => Time) closing time (Fin.last A.length)
      rw [A.following_last, Fin.lastCases_last]
    · change RoofTime (bank (A.following child k.castSucc)) true 1 =
        Fin.lastCases (motive := fun _ => Time) closing time k.castSucc
      rw [A.following_castSucc, Fin.lastCases_castSucc]
      let e := bank (A.child k)
      let f (j : Fin ((Stack e).length + 1)) : Time := ⟨⟨e, j⟩, 1⟩
      have empty_slot : Fin.last (Stack e).length = 0 := by
        apply Fin.ext
        change (Stack e).length = 0
        rw [show Stack e = [] from empty k]
        rfl
      exact congrArg f empty_slot
  have corners (i : Fin (A.length + 1)) (flag : Bool) (s : Time) :
      EndAt flag s.1 s.2 = roof i ↔
        (flag = (preceding i).2.1 ∧ s = prevTime i) ∨ (flag = true ∧ s = nextTime i) := by
    let p := preceding i
    let q := next i
    let w := (D).boundaryEndVertex Retain (contour.cycle.point (A.visit i))
    let x := Map ((D).vertexPoint Retain w)
    have nonroot : (D).contourOriginalVertex Selection contour (A.visit i) ∉ (Fcut).parents.roots :=
      (A.at_visit i).1.symm ▸ parent.property
    have h := K.compatibleContourSourceOnlyRoofVertex_baseMark_iff_of_germs compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W p.1 q
      p.2.1 true p.2.2 true (A.visit i) (prev_spec i).1 (next_germ i) nonroot
    have h' (e : Attachment) (side : Bool) (t : ParamAt e) := h e side t
    have one : finiteSlotParameterize true 0 = 1 := unitInterval.symm_zero
    have names (e : Attachment) (side : Bool) (t : ParamAt e) : Base e side t = x ↔
        ((⟨e, t⟩ : Σ b : Attachment, ParamAt b) =
          ⟨bank p.1, finiteSlotParameterize p.2.2 0⟩ ∧ side = p.2.1) ∨
        ((⟨e, t⟩ : Σ b : Attachment, ParamAt b) = ⟨bank q, 1⟩ ∧ side = true) := by
      simpa only [one] using h' e side t
    have nodup := K.compatibleContourBankStack_nodup compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour
    have equivalent := MetricGluing.bankStackEndpoint_eq_base_iff_two_marks Pieces Stack Base Gap
      nodup x (bank p.1) (bank q) p.2.1 true (finiteSlotParameterize p.2.2 0) 1 names flag s
    rw [show RoofTime (bank p.1) p.2.1 (finiteSlotParameterize p.2.2 0) = prevTime i from
      (prev_spec i).2, show RoofTime (bank q) true 1 = nextTime i from next_spec i] at equivalent
    exact equivalent

  have finalTime : nextTime (Fin.last A.length) = closing := by
    change Fin.lastCases (motive := fun _ => Time) closing time (Fin.last A.length) = closing
    exact Fin.lastCases_last
  have midTime (i : Fin A.length) : nextTime i.castSucc = time i := by
    change Fin.lastCases (motive := fun _ => Time) closing time i.castSucc = time i
    exact Fin.lastCases_castSucc i
  have roof_incident (i : Fin (A.length + 1)) (flag : Bool) (s : Time)
      (h : EndAt flag s.1 s.2 = roof i) : s = opening ∨ s = closing ∨ ∃ k, s = time k := by
    rcases (corners i flag s).mp h with ⟨_, t⟩ | ⟨_, t⟩
    · revert t
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Or.inl
      · exact fun h => Or.inr (Or.inr ⟨j, h⟩)
    · revert t
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact fun h => Or.inr (Or.inl (h.trans finalTime))
      · exact fun h => Or.inr (Or.inr ⟨j, h.trans (midTime j)⟩)
  have roof_unique : Function.Injective roof := by
    intro i j same
    let copy (k : Fin (A.length + 1)) := (D).boundaryEndVertex Retain
      (contour.cycle.point (A.visit k))
    have value : Map ((D).vertexPoint Retain (copy i)) = Map ((D).vertexPoint Retain (copy j)) :=
      eq_of_heq (Sigma.mk.inj same).2
    have nonroot : (D).contourOriginalVertex Selection contour (A.visit i) ∉ (Fcut).parents.roots :=
      (A.at_visit i).1.symm ▸ parent.property
    have below := K.compatibleContourRoofVertex_height_lt_of_nonroot compact nonempty R no_boundary
      level higher M positive inner_disk beta acute (copy i) nonroot
    have equal := K.compatibleMeshWholeMap_injective_at compact nonempty R no_boundary level higher
      M positive inner_disk beta acute W ((D).vertexPoint Retain (copy i)) below
      ((D).vertexPoint Retain (copy j)) value
    exact A.visit.injective ((D).boundaryCycle_vertices_injective Retain contour.cycle contour.closes
      ((D).vertexPoint_injective Retain equal))
  have bend_tag : bend.1 = some event := by
    have member : event ∈ Stack b := last_event.symm ▸ List.mem_append_right later List.mem_cons_self
    exact congrArg Sigma.fst (MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap
      false opening b event member true 0 open_name.1)
  have different (i : Fin (A.length + 1)) : bend ≠ roof i := by
    intro equal
    have impossible : some event = (none : Option Event) :=
      bend_tag.symm.trans (congrArg Sigma.fst equal)
    cases impossible
  let H := MetricGluing.BankStackCyclicClass.ofSingleBendRunWithSides bend roof opening closing time
    false true rfl ((corners 0 true opening).mpr (Or.inl ⟨rfl, rfl⟩))
    (fun i => (corners i.castSucc true (time i)).mpr (Or.inr ⟨rfl, (midTime i).symm⟩))
    (fun i => (corners i.succ false (time i)).mpr (Or.inl ⟨rfl, rfl⟩))
    ((corners (Fin.last A.length) true closing).mpr (Or.inr ⟨rfl, finalTime.symm⟩))
    bend_transfer.1.symm (fun flag s h => (bend_transfer.2 flag s h).2) roof_incident
  exact ⟨A, H, rfl, fun _ => rfl, rfl, rfl, empty, ⟨before, child_end⟩,
    MetricGluing.BankStackCyclicClass.singleCenter_injective bend roof roof_unique different⟩

end Unfoldings.ConvexRoof
