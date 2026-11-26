module

public import Unfoldings.FewestNets.ThreeExitGraftRoofRun
public import Unfoldings.FewestNets.ThreeExitGraftTipIncidence
public import Unfoldings.FewestNets.ThreeExitGraftCrossBlockClasses


/-! The cyclic class containing a source tip and its first child. -/

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

local instance graftTipAndChildClassIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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
local notation "SourceOfNonroot[" e "]" =>
  TriangleComplex.positiveContourVertex_nonroot D Selection S.contour e
local notation "SourceEdge[" e "]" => (Sum.inl (Subtype.mk SourceOf[e]
  (TriangleComplex.positiveContourVertex_nonroot D Selection S.contour e)) : Attachment)
local notation "BankAt[" e "]" => PotentialCutForest.contourSourceRay Fcut S.contour S.starts e
local notation "MovedAt[" e "]" => PotentialCutForest.contourSourceOpenedRay Fcut S.contour S.starts e
local notation "models" => (fun e : Event => Model[e])
local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams Left Right
local notation "Point" => MetricGluing.point Pieces Banks
local notation "RoofSite" => Edge × Bool × Bool
local notation "SiteTime" => contourGraftRoofSiteTime S
local notation "AtSite[" a "]" => Germ (Prod.fst a) (Prod.fst (Prod.snd a))
  (Prod.snd (Prod.snd a))

set_option maxHeartbeats 2700000 in
-- The source tip adds a third exterior slot to the original leading roof run.
/-- A positive parent source and its oldest descendant gap enclose the leading
roof wedges in one exact cyclic seam class. -/
theorem exists_contourGraftTipAndChildClass
    (source event : Event) (child : Edge)
    (at_parent : (Fcut).parents.parent child.val = SourceOf[source])
    (in_child : (Fcut).parents.Ancestor SourceOf[event] child.val)
    (tip_geometry : OrientedBankGap BankAt[source] MovedAt[source])
    (bend_geometry : OrientedBankGap BankAt[event] MovedAt[event])
    (later : List Event) (shape : Stack SourceEdge[source] = later ++ [event, source]) :
    let parent : Edge := ⟨SourceOf[source], SourceOfNonroot[source]⟩
    let first := finRotate (S.contour.length + 1) (Interval[parent.val,parent.property]).enter
    let last := (Interval[child.val,child.property]).enter
    let a := FiniteBank[child.val,child.property]
    let b := SourceEdge[source]
    ∃ (A : (D).ContourParentWedgeRun Selection S.contour (Fcut).boundary_roots S.starts
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
      ((D).contourEdgeGapStack_ordered Selection S.contour parent.val).reverse
    rw [shape] at sorted member
    rcases List.mem_append.mp member with in_before | last_two
    · exact ((List.pairwise_append.mp sorted).2.2 e in_before event List.mem_cons_self).le
    · rcases List.mem_cons.mp last_two with eq | last
      · exact eq.symm ▸ le_rfl
      · exact (diff (congrArg (fun q : Event => SourceOf[q]) (List.mem_singleton.mp last))).elim
  have at_child : event ∈ Stack a :=
    ((D).mem_contourSavedGapStack Selection S.contour child.val event).mpr in_child
  have oldest_child (e : Event) (member : e ∈ Stack a) : event.val.val ≤ e.val.val := by
    have in_child := ((D).mem_contourSavedGapStack Selection S.contour child.val e).mp member
    apply oldest e
    · exact ((D).mem_contourSavedGapStack Selection S.contour parent.val e).mpr
        (in_child.trans (Fcut).parents (parent_eq ▸ (Fcut).parents.ancestor_parent child.val))
    · intro equal
      exact (Fcut).parents.not_ancestor_parent_self child.property
        (parent_eq.symm ▸ (equal ▸ in_child))
  obtain ⟨before, after, child_eq⟩ := List.append_of_mem at_child
  have no_later : after = [] := by
    by_contra! present
    obtain ⟨e, member⟩ := List.exists_mem_of_ne_nil after present
    have sorted : (Stack a).Pairwise (fun a b => b.val.val < a.val.val) :=
      ((D).contourEdgeGapStack_ordered Selection S.contour child.val).reverse
    have out := (List.pairwise_cons.mp (List.pairwise_append.mp (child_eq ▸ sorted)).2.1).1
      e member
    exact (not_lt_of_ge (oldest_child e
      (child_eq.symm ▸ List.mem_append_right before (List.mem_cons_of_mem event member)))) out
  have child_end : Stack a = before ++ [event] := by simpa only [no_later] using child_eq
  obtain ⟨A, empty⟩ := (D).exists_contourFirstChildWedgeRun Selection S.contour (Fcut).boundary_roots
    S.starts parent child at_parent event in_child oldest
  obtain ⟨slot, event_name, source_name⟩ := MetricGluing.bankStack_exists_adjacent_gap_slot
    (Parameter := Param) Stack b 0 (show Stack b = later ++ event :: source :: [] from shape)
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
  have tip_names := MetricGluing.bankStack_last_gap_addresses (Parameter := Param)
    Stack b 0 source (later ++ [event]) source_last
  have tip_ends (flag : Bool) (s : Time) :
      EndAt flag s.1 s.2 = tip ↔ (flag = true ∧ s = closure) ∨ (flag = false ∧ s = opening) :=
    L.contourGraftTip_endpoint_iff S source tip_geometry at_tip
      closure opening source_name tip_names.1 flag s
  have exit_names := MetricGluing.bankStack_last_gap_addresses (Parameter := Param)
    Stack a 1 event before child_end
  have bend_ends := L.contourGraftGapBend_endpoint_transfer_of_parent S child parent at_parent event bend_geometry slot (Fin.last (Stack a).length)
    false true event_name exit_names.1
  have first_germ : Germ parent true false = (D).boundaryMate Retain (S.contour.cycle.point (A.visit 0)) :=
    ((D).contourParent_firstVisit_germ Selection S.contour (Fcut).boundary_roots S.starts
      parent.val parent.property).symm.trans
      (congrArg (fun j => (D).boundaryMate Retain (S.contour.cycle.point j)) A.at_first.symm)
  have last_germ : Germ child true true = S.contour.cycle.point (A.visit (Fin.last A.length)) := by
    change (D).boundaryTurn Retain ((D).boundaryTurn Retain
      (S.contour.cycle.point (Interval[child.val,child.property]).enter)) = _
    exact ((D).boundaryTurn_involutive Retain _).trans (congrArg S.contour.cycle.point A.at_last.symm)
  obtain ⟨_, corners⟩ := L.contourGraftRoofRun_endpoints S parent A
    (parent, true, false) (child, true, true) first_germ last_germ
  have site_times := contourGraftRoofRun_site_times_of_empty S parent A (parent, true, false)
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
      (S.contour.cycle.point (A.visit k))
    have value : Map ((D).vertexPoint Retain (copy i)) = Map ((D).vertexPoint Retain (copy j)) :=
      eq_of_heq (Sigma.mk.inj same).2
    have nonroot : (D).contourOriginalVertex Selection S.contour (A.visit i) ∉ (Fcut).parents.roots :=
      (A.at_visit i).1.symm ▸ parent.property
    have below := L.contourCutVertex_below S (copy i) nonroot
    have equal := L.fineMeshWholeMap_injective_at S.higher ((D).vertexPoint Retain (copy i)) ((D).vertexPoint Retain (copy j)) below value
    exact A.visit.injective ((D).boundaryCycle_vertices_injective Retain S.contour.cycle S.contour.closes
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

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
