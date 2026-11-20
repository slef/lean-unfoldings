module

public import Unfoldings.Roof.CompatibleContourSourceOnlyRoofRun
public import Unfoldings.Roof.CompatibleContourSourceOnlyTipIncidence
public import Unfoldings.Roof.CompatibleContourSourceOnlyCrossBlockClasses

/-! A source tip, leading roof wedges, and first descendant bend form the entry-side cycle. -/

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

local instance sourceOnlyTipAndChildIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlyTipAndChildWholeFintype : Fintype W.Index := W.finiteIndex

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


local notation "SourceOfNonroot[" e "]" =>
  TriangleComplex.positiveContourVertex_nonroot D Selection contour e
local notation "SourceEdge[" e "]" => FiniteBank[SourceOf[e],SourceOfNonroot[e]]

set_option maxHeartbeats 2700000 in
-- The source tip adds a third exterior slot to the original leading roof run.
/-- A positive parent source and its oldest descendant gap enclose the leading
roof wedges in one exact cyclic seam class. -/
theorem exists_compatibleContourSourceOnlyTipAndChildClass
    (source event : Event) (child : Edge)
    (at_parent : (Fcut).parents.parent child.val = SourceOf[source])
    (in_child : (Fcut).parents.Ancestor SourceOf[event] child.val)
    (tip_geometry : OrientedBankGap BankAt[source] MovedAt[source])
    (bend_geometry : OrientedBankGap BankAt[event] MovedAt[event])
    (later : List Event) (shape : Stack SourceEdge[source] = later ++ [event, source]) :
    let parent : Edge := ⟨SourceOf[source], SourceOfNonroot[source]⟩
    let first := finRotate (contour.length + 1) (Interval[parent.val,parent.property]).enter
    let last := (Interval[child.val,child.property]).enter
    let a := FiniteBank[child.val,child.property]
    let b := SourceEdge[source]
    ∃ (A : (D).ContourParentWedgeRun Selection contour (Fcut).boundary_roots starts
      parent.val first last)
      (H : MetricGluing.BankStackCyclicClass Pieces Stack Base Gap (A.length + 2))
      (slot : Fin ((Stack b).length + 1)),
      Named false ⟨b, slot⟩ 0 = ⟨b, some event, true, 0⟩ ∧
      Named true ⟨b, slot⟩ 0 = ⟨b, some source, false, 0⟩ ∧
      H.center 0 = ⟨some source, (models source).edgePoint false 0 0⟩ ∧
      H.center (Fin.last (A.length + 2)) = EndAt false ⟨b, slot⟩ 0 ∧
      (∀ i : Fin (A.length + 1), H.center i.castSucc.succ = RoofPoint[A.visit i]) ∧
      H.time = MetricGluing.BankStackCyclicClass.runTime
        (RoofTime b true 0) (RoofTime a true 1) (⟨⟨b, slot⟩, 0⟩ : Time)
        (fun i => ⟨⟨FiniteBank[(A.child i).val,(A.child i).property], 0⟩, 1⟩) ∧
      H.side = MetricGluing.BankStackCyclicClass.runSideWithEntry false ∧
      (∀ i, Stack FiniteBank[(A.child i).val,(A.child i).property] = []) ∧
      (∃ tail, Stack a = tail ++ [event]) ∧ Function.Injective H.center := by
  let parent : Edge := ⟨SourceOf[source], SourceOfNonroot[source]⟩
  have parent_eq : (Fcut).parents.parent child.val = parent.val := at_parent
  let a := FiniteBank[child.val,child.property]
  let b := SourceEdge[source]
  let opening := RoofTime b true 0
  let exit := RoofTime a true 1
  have oldest (e : Event) (member : e ∈ Stack b) (diff : SourceOf[e] ≠ parent.val) :
      event.val.val ≤ e.val.val := by
    have sorted : (Stack b).Pairwise (fun a b => b.val.val < a.val.val) :=
      ((D).contourEdgeGapStack_ordered Selection contour parent.val).reverse
    rw [shape] at sorted member
    rcases List.mem_append.mp member with in_before | last_two
    · exact ((List.pairwise_append.mp sorted).2.2 e in_before event List.mem_cons_self).le
    · rcases List.mem_cons.mp last_two with eq | last
      · exact eq.symm ▸ le_rfl
      · exact (diff (congrArg (fun q : Event => SourceOf[q]) (List.mem_singleton.mp last))).elim
  have at_child : event ∈ Stack a :=
    ((D).mem_contourSavedGapStack Selection contour child.val event).mpr in_child
  have oldest_child (e : Event) (member : e ∈ Stack a) : event.val.val ≤ e.val.val := by
    have in_child := ((D).mem_contourSavedGapStack Selection contour child.val e).mp member
    apply oldest e
    · exact ((D).mem_contourSavedGapStack Selection contour parent.val e).mpr
        (in_child.trans (Fcut).parents (parent_eq ▸ (Fcut).parents.ancestor_parent child.val))
    · intro equal
      exact (Fcut).parents.not_ancestor_parent_self child.property
        (parent_eq.symm ▸ (equal ▸ in_child))
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
    starts parent child at_parent event in_child oldest
  obtain ⟨slot, event_name, source_name⟩ := MetricGluing.bankStack_exists_adjacent_gap_slot
    (Parameter := ParamAt) Stack b 0 (show Stack b = later ++ event :: source :: [] from shape)
  let closure : Time := ⟨⟨b, slot⟩, 0⟩
  let tip : MetricGluing.Total Pieces := ⟨some source, (models source).edgePoint false 0 0⟩
  let bend := EndAt false closure.1 closure.2
  let roof (i : Fin (A.length + 1)) := RoofPoint[A.visit i]
  let bank (e : Edge) := FiniteBank[e.val,e.property]
  let time (i : Fin A.length) : Time := ⟨⟨bank (A.child i), 0⟩, 1⟩
  have source_last : Stack b = (later ++ [event]) ++ [source] := by
    rw [shape, List.append_assoc]
    rfl
  have at_tip : source ∈ Stack b :=
    source_last.symm ▸ List.mem_append_right _ List.mem_cons_self
  have tip_names := MetricGluing.bankStack_last_gap_addresses (Parameter := ParamAt)
    Stack b 0 source (later ++ [event]) source_last
  have tip_ends (flag : Bool) (s : Time) :
      EndAt flag s.1 s.2 = tip ↔ (flag = true ∧ s = closure) ∨ (flag = false ∧ s = opening) :=
    K.compatibleContourSourceOnlyTip_endpoint_iff compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models source tip_geometry at_tip
      closure opening source_name tip_names.1 flag s
  have exit_names := MetricGluing.bankStack_last_gap_addresses (Parameter := ParamAt)
    Stack a 1 event before child_end
  have bend_ends := K.compatibleContourSourceOnlyGapBend_endpoint_transfer_of_parent
    compact nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W
    models child parent at_parent event bend_geometry slot (Fin.last (Stack a).length)
    false true event_name exit_names.1
  have first_germ : Germ parent true false = (D).boundaryMate Retain (contour.cycle.point (A.visit 0)) :=
    ((D).contourParent_firstVisit_germ Selection contour (Fcut).boundary_roots starts
      parent.val parent.property).symm.trans
      (congrArg (fun j => (D).boundaryMate Retain (contour.cycle.point j)) A.at_first.symm)
  have last_germ : Germ child true true = contour.cycle.point (A.visit (Fin.last A.length)) := by
    change (D).boundaryTurn Retain ((D).boundaryTurn Retain
      (contour.cycle.point (Interval[child.val,child.property]).enter)) = _
    exact ((D).boundaryTurn_involutive Retain _).trans (congrArg contour.cycle.point A.at_last.symm)
  obtain ⟨_, corners⟩ := K.compatibleContourSourceOnlyRoofRun_endpoints compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W models parent A
    (parent, true, false) (child, true, true) first_germ last_germ
  have site_times := K.contourRoofRun_site_times_of_empty compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts parent A (parent, true, false)
    (child, true, true) empty
  let prevFlag (i : Fin (A.length + 1)) : Bool := Fin.cases true (fun _ => false) i
  let prevTime (i : Fin (A.length + 1)) : Time := Fin.cases opening time i
  let nextTime (i : Fin (A.length + 1)) : Time := Fin.lastCases exit time i
  have finalTime : nextTime (Fin.last A.length) = exit := by
    change Fin.lastCases (motive := fun _ => Time) exit time (Fin.last A.length) = exit
    exact Fin.lastCases_last
  have midTime (i : Fin A.length) : nextTime i.castSucc = time i := by
    change Fin.lastCases (motive := fun _ => Time) exit time i.castSucc = time i
    exact Fin.lastCases_castSucc i
  have nextFlag (i : Fin (A.length + 1)) :
      Fin.lastCases (motive := fun _ => Bool) true (fun _ => true) i = true := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Fin.lastCases_last
    · exact Fin.lastCases_castSucc j
  have exact_ends (i : Fin (A.length + 1)) (flag : Bool) (s : Time) :
      EndAt flag s.1 s.2 = roof i ↔
        (flag = prevFlag i ∧ s = prevTime i) ∨ (flag = true ∧ s = nextTime i) := by
    have h := corners i flag s
    have data := site_times i
    have child_one : finiteSlotParameterize true 0 = 1 := unitInterval.symm_zero
    rw [data.1, data.2.1, data.2.2.1, data.2.2.2, nextFlag i] at h
    change _ ↔
      (flag = prevFlag i ∧ s = prevTime i) ∨
      (flag = true ∧ s = Fin.lastCases (motive := fun _ => Time)
        (RoofTime a true (finiteSlotParameterize true 0)) time i) at h
    rw [child_one] at h
    exact h
  have roof_incident (i : Fin (A.length + 1)) (flag : Bool) (s : Time)
      (h : EndAt flag s.1 s.2 = roof i) : s = opening ∨ s = exit ∨ ∃ k, s = time k := by
    rcases (exact_ends i flag s).mp h with ⟨_, t⟩ | ⟨_, t⟩
    · revert t
      refine Fin.cases Or.inl (fun j eq => Or.inr (Or.inr ⟨j, eq⟩)) i
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
  have tag : bend.1 = some event := by
    have member : event ∈ Stack b := shape.symm ▸ List.mem_append_right later List.mem_cons_self
    exact congrArg Sigma.fst (MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap
      false closure b event member true 0 event_name)
  have different : source ≠ event := by
    intro same
    apply (Fcut).parents.not_ancestor_parent_self child.property
    exact at_parent.symm ▸ (same.symm ▸ in_child)
  have tip_bend : tip ≠ bend := by
    intro eq
    exact different (Option.some.inj ((congrArg Sigma.fst eq).trans tag))
  have tip_roof (i : Fin (A.length + 1)) : tip ≠ roof i := by
    intro eq
    cases congrArg Sigma.fst eq
  have bend_roof (i : Fin (A.length + 1)) : bend ≠ roof i := by
    intro eq
    have impossible : some event = (none : Option Event) := tag.symm.trans (congrArg Sigma.fst eq)
    cases impossible
  let H := MetricGluing.BankStackCyclicClass.ofRoofRunWithEntrySide tip bend roof opening exit
    closure time false ((tip_ends false opening).mpr (Or.inr ⟨rfl, rfl⟩))
    ((exact_ends 0 true opening).mpr (Or.inl ⟨rfl, rfl⟩))
    (fun i => (exact_ends i.castSucc true (time i)).mpr (Or.inr ⟨rfl, (midTime i).symm⟩))
    (fun i => (exact_ends i.succ false (time i)).mpr (Or.inl ⟨rfl, rfl⟩))
    ((exact_ends (Fin.last A.length) true exit).mpr (Or.inr ⟨rfl, finalTime.symm⟩))
    bend_ends.1.symm ((tip_ends true closure).mpr (Or.inl ⟨rfl, rfl⟩)) rfl
    (fun flag s eq => ((tip_ends flag s).mp eq).elim (fun h => Or.inr h.2) (fun h => Or.inl h.2))
    (fun flag s eq => ((bend_ends.2 flag s eq).2).elim Or.inr Or.inl) roof_incident
  have unique := MetricGluing.BankStackCyclicClass.runCenter_injective tip bend roof roof_unique
    tip_bend tip_roof bend_roof
  refine ⟨A, H, slot, event_name, source_name, rfl, ?_, ?_, rfl, rfl, empty, ⟨before, child_end⟩,
    unique⟩
  · rw [← Fin.succ_last (A.length + 1)]
    exact MetricGluing.BankStackCyclicClass.runCenter_last tip bend roof
  · exact MetricGluing.BankStackCyclicClass.runCenter_roof tip bend roof

end Unfoldings.ConvexRoof
