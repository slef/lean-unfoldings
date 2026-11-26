module

public import Unfoldings.FewestNets.ThreeExitGraftTipAndChildClass
public import Unfoldings.FewestNets.ThreeExitGraftTipSector
public import Unfoldings.Cone.MarkedSectorAngleAtlas
public import Unfoldings.FewestNets.ThreeExitGraftVertexRadii
public import Unfoldings.FewestNets.ThreeExitRoofSectorGerms
public import Unfoldings.FewestNets.ThreeExitGraftBendMarks
public import Unfoldings.FewestNets.ThreeExitGraftLabels
public import Unfoldings.Roof.PotentialContourJunctionAngles
public import Unfoldings.FewestNets.ThreeExitGraftRoofRun

/-! The original sectors glue to full planar balls at finite vertices. -/

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

local instance graftTipAndChildBallIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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
local notation "BankAt[" e "]" => PotentialCutForest.contourSourceRay Fcut S.contour S.starts e
local notation "MovedAt[" e "]" => PotentialCutForest.contourSourceOpenedRay Fcut S.contour S.starts e
local notation "models" => (fun e : Event => Model[e])
local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams Left Right
local notation "Point" => MetricGluing.point Pieces Banks
local notation "geometry" => S.gaps

local notation "Child" => Edge
local notation "LengthAt[" e "]" => TriangleComplex.positiveContourBankLength D Selection S.contour e
local notation "IndexAt[" v "," h "," e "," member "]" =>
  TriangleComplex.contourGapBankIndex D Selection S.contour v h e
    (Iff.mpr (TriangleComplex.mem_contourEdgeGapStack D Selection S.contour v e)
      (Iff.mp (TriangleComplex.mem_contourSavedGapStack D Selection S.contour v e) member))
local notation "BankLength[" v "," h "]" => TriangleComplex.boundaryBankLength D
  (TriangleComplex.contourParentBank D Selection S.contour (PotentialCutForest.boundary_roots Fcut)
    S.starts v h false)
local notation "AngleAt[" e "," i "]" => PotentialCutForest.contourSourceBankFanAngle Fcut S.contour S.starts e i
local notation "Q" => SpatialEnvelope.FloorMesh.roof T
  (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M S.higher)
local notation "RoofSite" => Edge × Bool × Bool
local notation "SiteTime" => contourGraftRoofSiteTime S
local notation "AtSite[" a "]" => Germ (Prod.fst a) (Prod.fst (Prod.snd a))
  (Prod.snd (Prod.snd a))
local notation "NamedSlot" => (Σ e : Edge,
  Fin (List.length (Stack FiniteBank[Subtype.val e,Subtype.property e]) + 1) × Bool)
local notation "Defect[" v "]" => TriangleComplex.interiorAngularDefect D Set.univ v

private theorem if_bend_side {X : Type*} (b side : Bool) (x y : X) :
    (if (if b then side else !side) then x else y) = (if b = side then x else y) := by
  cases b <;> cases side <;> rfl

/-- A finite registered slot measured from the specified origin. -/
private def timedSlot (s : NamedSlot) (t : unitInterval) : Time :=
  ⟨⟨FiniteBank[s.1.val,s.1.property], s.2.1⟩, finiteSlotParameterize s.2.2 t⟩

include L in
private theorem marked_gap_at_parent (child parent : Edge)
    (name : (Fcut).parents.parent child.val = parent.val)
    (e : Event) (here : e ∈ Stack FiniteBank[child.val,child.property])
    (above : e ∈ Stack FiniteBank[parent.val,parent.property])
    (strict : ∀ k : Fin LengthAt[e], let B := BankAt[e]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ))
    (side : Bool) :
    let saved := AngleAt[e,IndexAt[parent.val,parent.property,e,above]]
    let θ := if side then saved else 2 * Real.pi - saved
    let mark (b : Bool) (t : unitInterval) :=
      if b = side then
        Gap FiniteBank[child.val,child.property] e here side (unitInterval.symm t)
      else Gap FiniteBank[parent.val,parent.property] e above side t
    let length (b : Bool) :=
      if b = side then BankLength[child.val,child.property]
      else BankLength[parent.val,parent.property]
    Nonempty (MarkedSectorGerm (Gap FiniteBank[parent.val,parent.property] e above side 0)
      θ mark length) := by
  obtain ⟨parent, nonroot⟩ := parent
  change (Fcut).parents.parent child.val = parent at name
  subst parent
  simpa only [if_bend_side] using
    L.contourGraftGapBend_markedSectorGerm S
        child.val child.property nonroot e here above strict side

local notation "SourceOfNonroot[" e "]" =>
  TriangleComplex.positiveContourVertex_nonroot D Selection S.contour e
local notation "SourceEdge[" e "]" => FiniteBank[SourceOf[e],SourceOfNonroot[e]]

set_option maxHeartbeats 5000000 in
-- Every member of the leading run and the two gaps uses its original slot coordinates.
/-- The exact source class with a positive descendant is an actual whole planar ball. -/
theorem contourGraftTipAndChild_planarBall
    (source event : Event) (child : Edge)
    (at_parent : (Fcut).parents.parent child.val = SourceOf[source])
    (inside : (Fcut).parents.Ancestor SourceOf[event] child.val)
    (later : List Event) (shape : Stack SourceEdge[source] = later ++ [event, source])
    (strict : ∀ k : Fin LengthAt[event], let B := BankAt[event]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ)) :
    HasMetricBallChart ℂ (Point ⟨some source, (models source).edgePoint false 0 0⟩) := by
  let (a : Attachment) : TopologicalSpace (Param a) :=
    (contourAttachmentMetric S a).toUniformSpace.toTopologicalSpace
  obtain ⟨A, H, slot, event_name, source_name, first_center, last_center, roof_center, route,
      flags, empty, ⟨rest, child_end⟩, distinct⟩ :=
    L.exists_contourGraftTipAndChildClass S source event child at_parent
      inside (geometry source) (geometry event) later shape
  let parent : Edge := ⟨SourceOf[source],SourceOfNonroot[source]⟩
  let n := A.length
  let above : Attachment := FiniteBank[parent.val,parent.property]
  let b := FiniteBank[child.val,child.property]
  let final := Fin.last (Stack b).length
  let closing : Time := ⟨⟨above, slot⟩, 0⟩
  let entrance : NamedSlot := ⟨parent, Fin.last (Stack above).length, false⟩
  let exit : NamedSlot := ⟨child, final, true⟩
  let wrap : NamedSlot := ⟨parent, slot, false⟩
  let internal (i : Fin n) : NamedSlot := ⟨A.child i, 0, true⟩
  let middle (i : Fin (n + 1)) : NamedSlot := Fin.lastCases exit internal i
  let schedule (i : Fin (n + 3)) : NamedSlot :=
    Fin.cases entrance (Fin.lastCases wrap middle) i
  let time (i : Fin (n + 3)) := timedSlot S (schedule i)
  have time0 (t : unitInterval) :
      time 0 t = ⟨⟨above, Fin.last (Stack above).length⟩, t⟩ := rfl
  have scheduleWrap : schedule (Fin.last (n + 1)).succ = wrap := by
    change Fin.lastCases wrap middle (Fin.last (n + 1)) = wrap
    exact Fin.lastCases_last
  have timeWrap (t : unitInterval) : time (Fin.last (n + 1)).succ t = ⟨⟨above, slot⟩, t⟩ := by
    change timedSlot S (schedule (Fin.last (n + 1)).succ) t = _
    rw [scheduleWrap]
    rfl
  have timeMid (i : Fin (n + 1)) :
      schedule i.castSucc.succ = middle i := by
    change Fin.lastCases wrap middle i.castSucc = middle i
    exact Fin.lastCases_castSucc i
  have timeExit (t : unitInterval) :
      time (Fin.last n).castSucc.succ t = ⟨⟨b, final⟩, unitInterval.symm t⟩ := by
    have same : schedule (Fin.last n).castSucc.succ = exit :=
      (timeMid (Fin.last n)).trans Fin.lastCases_last
    change timedSlot S (schedule (Fin.last n).castSucc.succ) t = _
    rw [same]
    rfl
  have timeInner (i : Fin n) (t : unitInterval) : time i.castSucc.castSucc.succ t =
      ⟨⟨FiniteBank[(A.child i).val,(A.child i).property], 0⟩, unitInterval.symm t⟩ := by
    have same : schedule i.castSucc.castSucc.succ = internal i :=
      (timeMid i.castSucc).trans (Fin.lastCases_castSucc i)
    change timedSlot S (schedule i.castSucc.castSucc.succ) t = _
    rw [same]
    rfl
  have origin (i : Fin (n + 3)) : H.time i = time i 0 := by
    rw [route]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [MetricGluing.BankStackCyclicClass.runTime_zero, time0]
      rfl
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · rw [MetricGluing.BankStackCyclicClass.runTime_closure, timeWrap]
      · refine Fin.lastCases ?_ (fun l => ?_) k
        · rw [MetricGluing.BankStackCyclicClass.runTime_exit, timeExit, unitInterval.symm_zero]
          rfl
        · rw [MetricGluing.BankStackCyclicClass.runTime_between, timeInner, unitInterval.symm_zero]
  obtain ⟨parameterize, time_at, at_zero, metric⟩ :=
    L.contourGraftCyclicFiniteSlots_trace_parameters S H schedule origin
  let lengthOf (s : NamedSlot) := BankLength[s.1.val,s.1.property]
  let len (i : Fin (n + 3)) := lengthOf (schedule i)
  have len_pos (i : Fin (n + 3)) : 0 < len i := (D).boundaryBankLength_pos _
  have len0 : len 0 = BankLength[parent.val,parent.property] := rfl
  have lenWrap : len (Fin.last (n + 1)).succ = BankLength[parent.val,parent.property] := by
    change lengthOf (schedule (Fin.last (n + 1)).succ) = lengthOf wrap
    rw [scheduleWrap]
  have lenExit : len (Fin.last n).castSucc.succ = BankLength[child.val,child.property] := by
    have same : schedule (Fin.last n).castSucc.succ = exit :=
      (timeMid (Fin.last n)).trans Fin.lastCases_last
    change lengthOf (schedule (Fin.last n).castSucc.succ) = lengthOf exit
    rw [same]
  have lenInner (i : Fin n) : len i.castSucc.castSucc.succ =
      BankLength[(A.child i).val,(A.child i).property] := by
    have same : schedule i.castSucc.castSucc.succ = internal i :=
      (timeMid i.castSucc).trans (Fin.lastCases_castSucc i)
    change lengthOf (schedule i.castSucc.castSucc.succ) = lengthOf (internal i)
    rw [same]
  have source_last : Stack above = (later ++ [event]) ++ [source] := by
    rw [shape, List.append_assoc]
    rfl
  have tip_member : source ∈ Stack above := source_last.symm ▸ List.mem_append_right _ List.mem_cons_self
  have bend_member : event ∈ Stack above := shape.symm ▸ List.mem_append_right later List.mem_cons_self
  have child_member : event ∈ Stack b := child_end.symm ▸ List.mem_append_right rest List.mem_cons_self
  let endpoint (side : Bool) (i : Fin (n + 3)) (t : unitInterval) :=
    EndAt side (time i t).1 (time i t).2
  let slotEnd (side : Bool) (q : Time) := EndAt side q.1 q.2
  have entrance_endpoints (t : unitInterval) :
      endpoint false 0 t = ⟨some source, Gap above source tip_member true t⟩ ∧
      endpoint true 0 t = ⟨none, Base above true t⟩ := by
    have names := MetricGluing.bankStack_last_gap_addresses (Parameter := Param)
      Stack above t source (later ++ [event]) source_last
    change slotEnd false (time 0 t) = _ ∧ slotEnd true (time 0 t) = _
    rw [time0]
    exact ⟨MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap false _
      above source tip_member true t names.1, MetricGluing.bankStackEndpoint_eq_of_base_address
      Stack Pieces Base Gap true _ above true t names.2⟩
  have exit_endpoints (t : unitInterval) :
      endpoint false (Fin.last n).castSucc.succ t =
        ⟨some event, Gap b event child_member true (unitInterval.symm t)⟩ ∧
      endpoint true (Fin.last n).castSucc.succ t = ⟨none, Base b true (unitInterval.symm t)⟩ := by
    have names := MetricGluing.bankStack_last_gap_addresses (Parameter := Param)
      Stack b (unitInterval.symm t) event rest child_end
    change slotEnd false (time (Fin.last n).castSucc.succ t) = _ ∧
      slotEnd true (time (Fin.last n).castSucc.succ t) = _
    rw [timeExit]
    exact ⟨MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap false _
      b event child_member true (unitInterval.symm t) names.1,
      MetricGluing.bankStackEndpoint_eq_of_base_address Stack Pieces Base Gap true _
        b true (unitInterval.symm t) names.2⟩
  have wrap_endpoints (t : unitInterval) : endpoint false (Fin.last (n + 1)).succ t =
      ⟨some event, Gap above event bend_member true t⟩ ∧
      endpoint true (Fin.last (n + 1)).succ t = ⟨some source, Gap above source tip_member false t⟩ := by
    let q : Time := ⟨⟨above, slot⟩, t⟩
    have event_at := MetricGluing.bankStackEndpointAddress_at_time Stack false
      closing.1 closing.2 t event true event_name
    have source_at := MetricGluing.bankStackEndpointAddress_at_time Stack true
      closing.1 closing.2 t source false source_name
    change slotEnd false (time (Fin.last (n + 1)).succ t) = _ ∧
      slotEnd true (time (Fin.last (n + 1)).succ t) = _
    rw [timeWrap]
    exact ⟨MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap false q
      above event bend_member true t event_at,
      MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap true q
        above source tip_member false t source_at⟩
  have internal_endpoints (i : Fin n) (t : unitInterval) :
      let c := FiniteBank[(A.child i).val,(A.child i).property]
      endpoint false i.castSucc.castSucc.succ t = ⟨none, Base c false (unitInterval.symm t)⟩ ∧
      endpoint true i.castSucc.castSucc.succ t = ⟨none, Base c true (unitInterval.symm t)⟩ := by
    let c := FiniteBank[(A.child i).val,(A.child i).property]
    let q : Time := ⟨⟨c, 0⟩, unitInterval.symm t⟩
    have names := MetricGluing.bankStack_empty_addresses (Parameter := Param) Stack c
      (unitInterval.symm t) (empty i)
    change slotEnd false (time i.castSucc.castSucc.succ t) = _ ∧
      slotEnd true (time i.castSucc.castSucc.succ t) = _
    rw [timeInner]
    exact ⟨MetricGluing.bankStackEndpoint_eq_of_base_address Stack Pieces Base Gap false q
      c false (unitInterval.symm t) names.1, MetricGluing.bankStackEndpoint_eq_of_base_address
      Stack Pieces Base Gap true q c true (unitInterval.symm t) names.2⟩
  let advance := finRotate (n + 3)
  let previous := advance.symm
  let last := (Fin.last (n + 1)).succ
  let firstWedge := (0 : Fin (n + 1)).castSucc.succ
  have lenLast : len last = BankLength[parent.val,parent.property] := lenWrap
  have prev_zero : previous 0 = last := by
    apply advance.symm_apply_eq.mpr
    exact ((congrArg advance (Fin.succ_last (n + 1))).trans finRotate_last).symm
  have prev_first : previous firstWedge = 0 :=
    advance.symm_apply_eq.mpr (finRotate_of_lt (Nat.zero_lt_succ (n + 1))).symm
  have prev_wedge (i : Fin n) : previous i.succ.castSucc.succ = i.castSucc.castSucc.succ := by
    apply advance.symm_apply_eq.mpr
    let h : i.val + 1 < n + 2 := by omega
    exact (finRotate_of_lt h).symm
  have prev_last : previous last = (Fin.last n).castSucc.succ :=
    advance.symm_apply_eq.mpr (finRotate_of_lt (Nat.lt_succ_self (n + 1))).symm
  have flag0 : H.side 0 = false := by
    rw [flags, MetricGluing.BankStackCyclicClass.runSideWithEntry_zero]
  have flagLast : H.side last = false := by
    rw [flags, MetricGluing.BankStackCyclicClass.runSideWithEntry_last]
  have flagWedge (i : Fin (n + 1)) : H.side i.castSucc.succ = true := by
    rw [flags, MetricGluing.BankStackCyclicClass.runSideWithEntry_roof]
  let inAt (i : Fin (n + 3)) (t : unitInterval) :=
    endpoint (!(H.side (previous i))) (previous i) t
  let outAt (i : Fin (n + 3)) (t : unitInterval) := endpoint (H.side i) i t
  let p := contourGraftRoofRunIncoming S A (parent, true, false)
  let q := contourGraftRoofRunOutgoing S A (child, true, true)
  let speed (e : Edge) := BankLength[e.val,e.property]
  let markSite (s : Edge × Bool × Bool) (t : unitInterval) : MetricGluing.Total Pieces :=
    ⟨none, Base (.inl s.1) s.2.1 (finiteSlotParameterize s.2.2 t)⟩
  have roof_left (i : Fin (n + 1)) (t : unitInterval) :
      inAt i.castSucc.succ t = markSite (p i) t ∧
      len (previous i.castSucc.succ) = speed (p i).1 := by
    refine Fin.cases ?_ (fun k => ?_) i
    · change endpoint (!(H.side (previous firstWedge))) (previous firstWedge) t = _ ∧ _
      rw [prev_first, flag0]
      exact ⟨(entrance_endpoints t).2, len0⟩
    · change endpoint (!(H.side (previous k.succ.castSucc.succ)))
        (previous k.succ.castSucc.succ) t = _ ∧ _
      rw [prev_wedge, flagWedge]
      exact ⟨(internal_endpoints k t).1, lenInner k⟩
  have roof_right (i : Fin (n + 1)) (t : unitInterval) :
      outAt i.castSucc.succ t = markSite (q i) t ∧ len i.castSucc.succ = speed (q i).1 := by
    refine Fin.lastCases ?_ (fun k => ?_) i
    · have site : q (Fin.last n) = (child, true, true) := by
        change Fin.lastCases (motive := fun _ => Edge × Bool × Bool) (child, true, true)
          (fun j => (A.child j, true, true)) (Fin.last n) = _
        exact Fin.lastCases_last
      change endpoint (H.side (Fin.last n).castSucc.succ) (Fin.last n).castSucc.succ t =
        markSite (q (Fin.last n)) t ∧ _
      rw [flagWedge, site]
      exact ⟨(exit_endpoints t).2, lenExit⟩
    · have site : q k.castSucc = (A.child k, true, true) := by
        change Fin.lastCases (motive := fun _ => Edge × Bool × Bool) (child, true, true)
          (fun j => (A.child j, true, true)) k.castSucc = _
        exact Fin.lastCases_castSucc k
      change endpoint (H.side k.castSucc.castSucc.succ) k.castSucc.castSucc.succ t =
        markSite (q k.castSucc) t ∧ _
      rw [flagWedge, site]
      exact ⟨(internal_endpoints k t).2, lenInner k⟩
  let defect := (D).interiorAngularDefect Set.univ parent.val
  let saved := AngleAt[event,IndexAt[parent.val,parent.property,event,bend_member]]
  let wedge (i : Fin (n + 1)) := (D).totalAngle Retain
    ((D).boundaryEndVertex Retain (S.contour.cycle.point (A.visit i)))
  let tail (i : Fin (n + 2)) : ℝ := Fin.lastCases saved wedge i
  let angle (i : Fin (n + 3)) : ℝ := Fin.cases defect tail i
  have angleLast : angle last = saved := by
    change Fin.lastCases saved wedge (Fin.last (n + 1)) = saved
    exact Fin.lastCases_last
  have angleWedge (i : Fin (n + 1)) : angle i.castSucc.succ = wedge i := by
    change Fin.lastCases saved wedge i.castSucc = wedge i
    exact Fin.lastCases_castSucc i
  have balance : saved + (∑ i, wedge i) + defect = 2 * Real.pi :=
    (Fcut).contourGraftFirstChild_angle_balance S.contour S.starts parent.val child.val
      parent.property child.property at_parent event inside bend_member A
  have full : (∑ i, angle i) = 2 * Real.pi := by
    rw [Fin.sum_univ_succ]
    change defect + (∑ i, tail i) = 2 * Real.pi
    rw [Fin.sum_univ_castSucc]
    have first : (∑ i : Fin (n + 1), tail i.castSucc) = ∑ i, wedge i :=
      Finset.sum_congr rfl (fun i _ => Fin.lastCases_castSucc i)
    rw [first, show tail (Fin.last (n + 1)) = saved from Fin.lastCases_last]
    linarith
  let flip (i : Fin (n + 3)) := decide (i = 0 ∨ i = last)
  have flip0 : flip 0 = true := by simp [flip]
  have flipLast : flip last = true := by simp [flip]
  have flipWedge (i : Fin (n + 1)) : flip i.castSucc.succ = false := by
    apply decide_eq_false
    rintro (at_zero | at_last)
    · have bad : i.val + 1 = 0 := congrArg (fun k : Fin (n + 3) => k.val) at_zero
      omega
    · have bad : i.val + 1 = n + 2 := congrArg (fun k : Fin (n + 3) => k.val) at_last
      have h := i.isLt
      omega
  let lengthAt (i : Fin (n + 3)) (b : Bool) : ℝ :=
    if b = flip i then len (previous i) else len i
  let SectorAt (i : Fin (n + 3)) (c : MetricGluing.Total Pieces) :=
    ∃ mark : Bool → unitInterval → Pieces c.1,
      Nonempty (MarkedSectorGerm c.2 (angle i) mark (lengthAt i)) ∧
      (∀ t, outAt i t = ⟨c.1, mark (!(flip i)) t⟩) ∧
      (∀ t, inAt i t = ⟨c.1, mark (flip i) t⟩)
  have gBend := marked_gap_at_parent L S child parent at_parent
    event child_member bend_member strict true
  let tip_mark (u : Bool) (t : unitInterval) := Gap above source tip_member (!u) t
  let tip_length (_ : Bool) := BankLength[parent.val,parent.property]
  let bend_mark (u : Bool) (t : unitInterval) :=
    if u then Gap b event child_member true (unitInterval.symm t)
    else Gap above event bend_member true t
  let bend_length (u : Bool) :=
    if u then BankLength[child.val,child.property] else BankLength[parent.val,parent.property]
  have tip_local : SectorAt 0 ⟨some source, (models source).edgePoint false 0 0⟩ := by
    have lens : tip_length = lengthAt 0 := by
      funext u
      cases u <;> simp only [tip_length, lengthAt, flip0, prev_zero, lenLast, len0,
        Bool.false_eq_true, ite_true, ite_false]
    have germ : Nonempty (MarkedSectorGerm ((models source).edgePoint false 0 0)
        (angle 0) tip_mark tip_length) :=
      L.contourGraftTip_markedSectorGerm S source tip_member
    refine ⟨tip_mark, lens ▸ germ, ?_, ?_⟩
    · intro t
      change endpoint (H.side 0) 0 t = _
      rw [flag0, flip0]
      exact (entrance_endpoints t).1
    · intro t
      change endpoint (!(H.side (previous 0))) (previous 0) t = _
      rw [prev_zero, flagLast, flip0]
      exact (wrap_endpoints t).2
  have bend_center : H.center last = ⟨some event, Gap above event bend_member true 0⟩ := by
    change H.center (Fin.last (n + 1)).succ = _
    rw [Fin.succ_last]
    exact last_center.trans
      (MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap false closing
        above event bend_member true 0 event_name)
  have bend_local : SectorAt last ⟨some event, Gap above event bend_member true 0⟩ := by
    have lens : bend_length = lengthAt last := by
      funext u
      cases u <;> simp only [bend_length, lengthAt, flipLast, prev_last, lenLast, lenExit,
        Bool.false_eq_true, ite_false, ite_true]
    have germ : Nonempty (MarkedSectorGerm (Gap above event bend_member true 0)
        saved bend_mark bend_length) := by
      simpa only [saved, bend_mark, bend_length, ite_true] using gBend
    refine ⟨bend_mark, lens ▸ (angleLast.symm ▸ germ), ?_, ?_⟩
    · intro t
      change endpoint (H.side last) last t = _
      rw [flagLast, flipLast]
      exact (wrap_endpoints t).1
    · intro t
      change endpoint (!(H.side (previous last))) (previous last) t = _
      rw [prev_last, flagWedge, flipLast]
      exact (exit_endpoints t).1
  have small_wedge (i : Fin (n + 1)) : wedge i < 2 * Real.pi := by
    obtain ⟨_, chart, _, _⟩ := bend_local
    have bend_pos := (Classical.choice chart).sector.angle_pos
    rw [angleLast] at bend_pos
    have tip_pos : 0 < defect := source.property.2
    have nonneg (j : Fin (n + 1)) : 0 ≤ wedge j := ((D).totalAngle_pos Retain _).le
    have bound : wedge i ≤ ∑ j, wedge j := Finset.single_le_sum
      (fun j _ => nonneg j) (Finset.mem_univ i)
    linarith
  have first_germ : Germ parent true false = (D).boundaryMate Retain (S.contour.cycle.point (A.visit 0)) :=
    ((D).contourParent_firstVisit_germ Selection S.contour (Fcut).boundary_roots S.starts
      parent.val parent.property).symm.trans
      (congrArg (fun j => (D).boundaryMate Retain (S.contour.cycle.point j)) A.at_first.symm)
  have last_germ : Germ child true true = S.contour.cycle.point (A.visit (Fin.last n)) := by
    change (D).boundaryTurn Retain ((D).boundaryTurn Retain
      (S.contour.cycle.point (Interval[child.val,child.property]).enter)) = _
    exact ((D).boundaryTurn_involutive Retain _).trans (congrArg S.contour.cycle.point A.at_last.symm)
  obtain ⟨germs, _⟩ := L.contourGraftRoofRun_endpoints S parent A
    (parent, true, false) (child, true, true) first_germ last_germ
  have roof_local (i : Fin (n + 1)) : SectorAt i.castSucc.succ RoofPoint[A.visit i] := by
    let left := p i
    let right := q i
    let mark (u : Bool) (t : unitInterval) := if u then
      Base (.inl right.1) right.2.1 (finiteSlotParameterize right.2.2 t)
      else Base (.inl left.1) left.2.1 (finiteSlotParameterize left.2.2 t)
    let length (u : Bool) := if u then speed right.1 else speed left.1
    have lens : length = lengthAt i.castSucc.succ := by
      funext u
      cases u
      · change speed left.1 = lengthAt i.castSucc.succ false
        unfold lengthAt
        rw [flipWedge, ite_eq_left rfl]
        exact (roof_left i 0).2.symm
      · change speed right.1 = lengthAt i.castSucc.succ true
        unfold lengthAt
        rw [flipWedge, ite_eq_right (Bool.noConfusion : true ≠ false)]
        exact (roof_right i 0).2.symm
    have nonroot : (D).contourOriginalVertex Selection S.contour (A.visit i) ∉ (Fcut).parents.roots :=
      (A.at_visit i).1.symm ▸ parent.property
    have original := L.contourRoofVertex_markedSectorGerm_of_germs S
      left.1 right.1 left.2.1 right.2.1 left.2.2 right.2.2 (A.visit i)
      (germs i).1 (germs i).2 nonroot (small_wedge i)
    have germ : Nonempty (MarkedSectorGerm (Map ((D).vertexPoint Retain
        ((D).boundaryEndVertex Retain (S.contour.cycle.point (A.visit i)))))
        (wedge i) mark length) := original
    refine ⟨mark, lens ▸ ((angleWedge i).symm ▸ germ), ?_, ?_⟩
    · intro t
      rw [flipWedge]
      exact (roof_right i t).1
    · intro t
      rw [flipWedge]
      exact (roof_left i t).1
  have all_sectors (i : Fin (n + 3)) : SectorAt i (H.center i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact first_center.symm ▸ tip_local
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · exact bend_center.symm ▸ bend_local
      · exact (roof_center k).symm ▸ roof_local k
  let atlas := MetricGluing.BankStackCyclicClass.MarkedAtlas.ofGerms Pieces Stack Base Gap H
    angle full parameterize at_zero len len_pos metric flip (fun i => by
      obtain ⟨mark, germ, out, enter⟩ := all_sectors i
      refine ⟨mark, germ, ?_, ?_⟩
      · intro t
        exact (congrArg (slotEnd (H.side i)) (time_at i t)).trans (out t)
      · intro t
        exact (congrArg (slotEnd (!(H.side (previous i)))) (time_at (previous i) t)).trans (enter t))
  obtain ⟨r, rpos, cover⟩ := L.contourGraft_piece_ball_cover S
    (H.center 0)
  have chart := atlas.hasMetricBallChart distinct
    (L.isClosedEmbedding_contourBaseMark S)
    (isClosedEmbedding_contourGapMark S) rpos cover
  exact first_center ▸ chart

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
