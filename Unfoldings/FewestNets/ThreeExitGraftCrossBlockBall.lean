module

public import Unfoldings.FewestNets.ThreeExitGraftCrossBlockClasses
public import Unfoldings.Cone.MarkedSectorBankStack
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

local instance graftCrossBlockBallIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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

set_option maxHeartbeats 5000000 in
-- The four dependent slot families and their finite transports use the same original class.
/-- The actual cross-block class has a whole planar metric ball at its outgoing join. -/
theorem contourGraftCrossBlock_planarBall
    (parent old_child new_child : Edge)
    (old_parent : (Fcut).parents.parent old_child.val = parent.val)
    (new_parent : (Fcut).parents.parent new_child.val = parent.val)
    (different : old_child.val ≠ new_child.val) (old new : Event)
    (old_in : (Fcut).parents.Ancestor SourceOf[old] old_child.val)
    (new_in : (Fcut).parents.Ancestor SourceOf[new] new_child.val)
    (strict : ∀ (e : Event) (k : Fin LengthAt[e]), let B := BankAt[e]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ))
    (pre post : List Event)
    (adjacent : Stack FiniteBank[parent.val,parent.property] = pre ++ new :: old :: post) :
    let above := FiniteBank[parent.val,parent.property]
    ∃ (slot : Fin ((Stack above).length + 1)),
      Named false ⟨above, slot⟩ 0 = ⟨above, some new, true, 0⟩ ∧
      Named true ⟨above, slot⟩ 0 = ⟨above, some old, false, 0⟩ ∧
      HasMetricBallChart ℂ (Point (EndAt true ⟨above, slot⟩ 0)) := by
  let (a : Attachment) : TopologicalSpace (Param a) :=
    (contourAttachmentMetric S a).toUniformSpace.toTopologicalSpace
  obtain ⟨A, H, slot, new_out, old_out, first_center, last_center, roof_center, route, flags,
      empty, interval, unique⟩ :=
    L.exists_contourGraftCrossBlockData S parent old_child new_child old_parent
      new_parent different old new old_in new_in (geometry old) (geometry new) pre post adjacent
  let n := A.length
  let above := FiniteBank[parent.val,parent.property]
  let a := FiniteBank[old_child.val,old_child.property]
  let b := FiniteBank[new_child.val,new_child.property]
  let final := Fin.last (Stack b).length
  let closing : Time := ⟨⟨above, slot⟩, 0⟩
  let entrance : NamedSlot := ⟨old_child, 0, true⟩
  let exit : NamedSlot := ⟨new_child, final, true⟩
  let wrap : NamedSlot := ⟨parent, slot, false⟩
  let internal (i : Fin n) : NamedSlot := ⟨A.child i, 0, true⟩
  let middle (i : Fin (n + 1)) : NamedSlot := Fin.lastCases exit internal i
  let schedule (i : Fin (n + 3)) : NamedSlot :=
    Fin.cases entrance (Fin.lastCases wrap middle) i
  let time (i : Fin (n + 3)) := timedSlot S (schedule i)
  have time0 (t : unitInterval) : time 0 t = ⟨⟨a, 0⟩, unitInterval.symm t⟩ := rfl
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
    · rw [MetricGluing.BankStackCyclicClass.runTime_zero, time0, unitInterval.symm_zero]
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · rw [MetricGluing.BankStackCyclicClass.runTime_closure, timeWrap]
      · refine Fin.lastCases ?_ (fun l => ?_) k
        · rw [MetricGluing.BankStackCyclicClass.runTime_exit, timeExit, unitInterval.symm_zero]
        · rw [MetricGluing.BankStackCyclicClass.runTime_between, timeInner, unitInterval.symm_zero]
  obtain ⟨parameterize, time_at, at_zero, metric⟩ :=
    L.contourGraftCyclicFiniteSlots_trace_parameters S H schedule origin
  let lengthOf (s : NamedSlot) := BankLength[s.1.val,s.1.property]
  let len (i : Fin (n + 3)) := lengthOf (schedule i)
  have len_pos (i : Fin (n + 3)) : 0 < len i := (D).boundaryBankLength_pos _
  have len0 : len 0 = BankLength[old_child.val,old_child.property] := rfl
  have lenWrap : len (Fin.last (n + 1)).succ = BankLength[parent.val,parent.property] := by
    change lengthOf (schedule (Fin.last (n + 1)).succ) = lengthOf wrap
    rw [scheduleWrap]
  have lenExit : len (Fin.last n).castSucc.succ = BankLength[new_child.val,new_child.property] := by
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
  have old_member : old ∈ Stack above := show Valid ⟨above, some old, false, 0⟩ from
    old_out ▸ MetricGluing.bankStackEndpointAddress_valid Stack true closing.1 closing.2
  have new_member : new ∈ Stack above := show Valid ⟨above, some new, true, 0⟩ from
    new_out ▸ MetricGluing.bankStackEndpointAddress_valid Stack false closing.1 closing.2
  have old_here : old ∈ Stack a := ((D).mem_contourSavedGapStack Selection S.contour
    old_child.val old).mpr old_in
  have new_here : new ∈ Stack b := ((D).mem_contourSavedGapStack Selection S.contour
    new_child.val new).mpr new_in
  obtain ⟨⟨older, old_shape⟩, ⟨newer, new_shape⟩⟩ := (D).contourSavedGapStack_boundary_events
    Selection S.contour (Fcut).boundary_roots S.starts parent.val old_child.val new_child.val
    parent.property old_child.property new_child.property old_parent new_parent different
    old new old_in new_in pre post adjacent
  let endpoint (side : Bool) (i : Fin (n + 3)) (t : unitInterval) :=
    EndAt side (time i t).1 (time i t).2
  let slotEnd (side : Bool) (q : Time) := EndAt side q.1 q.2
  have entrance_endpoints (t : unitInterval) :
      endpoint false 0 t = ⟨none, Base a false (unitInterval.symm t)⟩ ∧
      endpoint true 0 t = ⟨some old, Gap a old old_here false (unitInterval.symm t)⟩ := by
    let q : Time := ⟨⟨a, 0⟩, unitInterval.symm t⟩
    have names := MetricGluing.bankStack_first_gap_addresses (Parameter := Param)
      Stack a (unitInterval.symm t) old older old_shape
    change slotEnd false (time 0 t) = _ ∧ slotEnd true (time 0 t) = _
    rw [time0]
    exact ⟨MetricGluing.bankStackEndpoint_eq_of_base_address Stack Pieces Base Gap false q
      a false (unitInterval.symm t) names.1, MetricGluing.bankStackEndpoint_eq_of_gap_address
      Stack Pieces Base Gap true q a old old_here false (unitInterval.symm t) names.2⟩
  have exit_endpoints (t : unitInterval) :
      endpoint false (Fin.last n).castSucc.succ t =
        ⟨some new, Gap b new new_here true (unitInterval.symm t)⟩ ∧
      endpoint true (Fin.last n).castSucc.succ t = ⟨none, Base b true (unitInterval.symm t)⟩ := by
    let q : Time := ⟨⟨b, final⟩, unitInterval.symm t⟩
    have names := MetricGluing.bankStack_last_gap_addresses (Parameter := Param)
      Stack b (unitInterval.symm t) new newer new_shape
    change slotEnd false (time (Fin.last n).castSucc.succ t) = _ ∧
      slotEnd true (time (Fin.last n).castSucc.succ t) = _
    rw [timeExit]
    exact ⟨MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap false q
      b new new_here true (unitInterval.symm t) names.1,
      MetricGluing.bankStackEndpoint_eq_of_base_address Stack Pieces Base Gap true q
        b true (unitInterval.symm t) names.2⟩
  have wrap_endpoints (t : unitInterval) :
      endpoint false (Fin.last (n + 1)).succ t = ⟨some new, Gap above new new_member true t⟩ ∧
      endpoint true (Fin.last (n + 1)).succ t = ⟨some old, Gap above old old_member false t⟩ := by
    let q : Time := ⟨⟨above, slot⟩, t⟩
    have named_left := MetricGluing.bankStackEndpointAddress_at_time Stack false
      closing.1 closing.2 t new true new_out
    have named_right := MetricGluing.bankStackEndpointAddress_at_time Stack true
      closing.1 closing.2 t old false old_out
    change slotEnd false (time (Fin.last (n + 1)).succ t) = _ ∧
      slotEnd true (time (Fin.last (n + 1)).succ t) = _
    rw [timeWrap]
    exact ⟨MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap false q
      above new new_member true t named_left, MetricGluing.bankStackEndpoint_eq_of_gap_address
      Stack Pieces Base Gap true q above old old_member false t named_right⟩
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
  have flag0 : H.side 0 = true := by
    rw [flags, MetricGluing.BankStackCyclicClass.runSide_zero]
  have flagLast : H.side last = false := by
    rw [flags, MetricGluing.BankStackCyclicClass.runSide_last]
  have flagWedge (i : Fin (n + 1)) : H.side i.castSucc.succ = true := by
    rw [flags, MetricGluing.BankStackCyclicClass.runSide_roof]
  let inAt (i : Fin (n + 3)) (t : unitInterval) :=
    endpoint (!(H.side (previous i))) (previous i) t
  let outAt (i : Fin (n + 3)) (t : unitInterval) := endpoint (H.side i) i t
  have atWedgeLeft (i : Fin (n + 1)) (t : unitInterval) :
      inAt i.castSucc.succ t =
        ⟨none, Base (.inl (A.previous old_child i)) false (unitInterval.symm t)⟩ ∧
      len (previous i.castSucc.succ) =
        BankLength[(A.previous old_child i).val,(A.previous old_child i).property] := by
    refine Fin.cases ?_ (fun k => ?_) i
    · change endpoint (!(H.side (previous firstWedge))) (previous firstWedge) t = _ ∧ _
      rw [prev_first, flag0]
      exact ⟨(entrance_endpoints t).1, len0⟩
    · change endpoint (!(H.side (previous k.succ.castSucc.succ)))
        (previous k.succ.castSucc.succ) t = _ ∧ _
      rw [prev_wedge, flagWedge]
      exact ⟨(internal_endpoints k t).1, lenInner k⟩
  have atWedgeRight (i : Fin (n + 1)) (t : unitInterval) :
      outAt i.castSucc.succ t =
        ⟨none, Base (.inl (A.following new_child i)) true (unitInterval.symm t)⟩ ∧
      len i.castSucc.succ =
        BankLength[(A.following new_child i).val,(A.following new_child i).property] := by
    refine Fin.lastCases ?_ (fun k => ?_) i
    · change endpoint (H.side (Fin.last n).castSucc.succ) (Fin.last n).castSucc.succ t = _ ∧ _
      rw [flagWedge, A.following_last]
      exact ⟨(exit_endpoints t).2, lenExit⟩
    · change endpoint (H.side k.castSucc.castSucc.succ) k.castSucc.castSucc.succ t = _ ∧ _
      rw [flagWedge, A.following_castSucc]
      exact ⟨(internal_endpoints k t).2, lenInner k⟩
  let old_angle := 2 * Real.pi - AngleAt[old,IndexAt[parent.val,parent.property,old,old_member]]
  let new_angle := AngleAt[new,IndexAt[parent.val,parent.property,new,new_member]]
  let wedge (i : Fin (n + 1)) := (D).totalAngle Retain
    ((D).boundaryEndVertex Retain (S.contour.cycle.point (A.visit i)))
  let inside (i : Fin (n + 2)) : ℝ := Fin.lastCases new_angle wedge i
  let angle (i : Fin (n + 3)) : ℝ := Fin.cases old_angle inside i
  have angleLast : angle last = new_angle := by
    change Fin.lastCases new_angle wedge (Fin.last (n + 1)) = new_angle
    exact Fin.lastCases_last
  have angleWedge (i : Fin (n + 1)) : angle i.castSucc.succ = wedge i := by
    change Fin.lastCases new_angle wedge i.castSucc = wedge i
    exact Fin.lastCases_castSucc i
  have ordered : old.val.val ≤ new.val.val := by
    have sorted : (Stack above).Pairwise (fun a b => b.val.val < a.val.val) :=
      ((D).contourEdgeGapStack_ordered Selection S.contour parent.val).reverse
    rw [adjacent] at sorted
    exact ((List.pairwise_cons.mp (List.pairwise_append.mp sorted).2.1).1 old
      List.mem_cons_self).le
  have balance : old_angle + (∑ i, wedge i) + new_angle = 2 * Real.pi :=
    (Fcut).contourGraftCrossBlock_angle_balance S.contour S.starts parent.val parent.property old new
      old_member new_member ordered _ _ A interval
  have full : (∑ i, angle i) = 2 * Real.pi := by
    rw [Fin.sum_univ_succ]
    change old_angle + (∑ i, inside i) = 2 * Real.pi
    rw [Fin.sum_univ_castSucc]
    have first : (∑ i : Fin (n + 1), inside i.castSucc) = ∑ i, wedge i :=
      Finset.sum_congr rfl (fun i _ => Fin.lastCases_castSucc i)
    rw [first, show inside (Fin.last (n + 1)) = new_angle from Fin.lastCases_last]
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
  have old_center : H.center 0 = ⟨some old, Gap above old old_member false 0⟩ :=
    first_center.trans (MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap
      true closing above old old_member false 0 old_out)
  have new_center : H.center last = ⟨some new, Gap above new new_member true 0⟩ := by
    change H.center (Fin.last (n + 1)).succ = _
    rw [Fin.succ_last]
    exact last_center.trans (MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap
      false closing above new new_member true 0 new_out)
  have gOld := marked_gap_at_parent L S old_child parent old_parent
    old old_here old_member (strict old) false
  have gNew := marked_gap_at_parent L S new_child parent new_parent
    new new_here new_member (strict new) true
  let old_mark (b : Bool) (t : unitInterval) :=
    if b = false then Gap a old old_here false (unitInterval.symm t)
    else Gap above old old_member false t
  let old_length (b : Bool) :=
    if b = false then BankLength[old_child.val,old_child.property]
    else BankLength[parent.val,parent.property]
  let new_mark (u : Bool) (t : unitInterval) :=
    if u then Gap b new new_here true (unitInterval.symm t)
    else Gap above new new_member true t
  let new_length (u : Bool) :=
    if u then BankLength[new_child.val,new_child.property]
    else BankLength[parent.val,parent.property]
  have old_local : SectorAt 0 ⟨some old, Gap above old old_member false 0⟩ := by
    have lens : old_length = lengthAt 0 := by
      funext side
      cases side <;> simp only [old_length, lengthAt, flip0, len0, prev_zero, lenLast,
        Bool.true_eq_false,
        Bool.false_eq_true, ite_false, ite_true]
    have germ : Nonempty (MarkedSectorGerm (Gap above old old_member false 0)
        (angle 0) old_mark old_length) := by
      simpa only [angle, Fin.cases_zero, old_angle, old_mark, old_length, Bool.false_eq_true,
        ite_false] using gOld
    refine ⟨old_mark, lens ▸ germ, ?_, ?_⟩
    · intro t
      change endpoint (H.side 0) 0 t = _
      rw [flag0, flip0]
      exact (entrance_endpoints t).2
    · intro t
      change endpoint (!(H.side (previous 0))) (previous 0) t = _
      rw [prev_zero, flagLast, flip0]
      exact (wrap_endpoints t).2
  have new_local : SectorAt last ⟨some new, Gap above new new_member true 0⟩ := by
    have lens : new_length = lengthAt last := by
      funext side
      cases side <;> simp only [new_length, lengthAt, flipLast, lenLast, prev_last, lenExit,
        Bool.false_eq_true, ite_false, ite_true]
    have germ : Nonempty (MarkedSectorGerm (Gap above new new_member true 0)
        new_angle new_mark new_length) := by
      simpa only [new_angle, new_mark, new_length, ite_true] using gNew
    refine ⟨new_mark, lens ▸ (angleLast.symm ▸ germ), ?_, ?_⟩
    · intro t
      change endpoint (H.side last) last t = _
      rw [flagLast, flipLast]
      exact (wrap_endpoints t).1
    · intro t
      change endpoint (!(H.side (previous last))) (previous last) t = _
      rw [prev_last, flagWedge, flipLast]
      exact (exit_endpoints t).1
  have roof_local (i : Fin (n + 1)) : SectorAt i.castSucc.succ RoofPoint[A.visit i] := by
    let p := A.previous old_child i
    let q := A.following new_child i
    let edge (b : Bool) : Edge := if b then q else p
    let mark (b : Bool) (t : unitInterval) := Base (.inl (edge b)) b (unitInterval.symm t)
    let speed (b : Bool) := BankLength[(edge b).val,(edge b).property]
    have nonroot : (D).contourOriginalVertex Selection S.contour (A.visit i) ∉ (Fcut).parents.roots :=
      (A.at_visit i).1.symm ▸ parent.property
    have first_len := (atWedgeLeft i 0).2
    have last_len := (atWedgeRight i 0).2
    have lens : speed = lengthAt i.castSucc.succ := by
      funext b
      cases b
      · change BankLength[p.val,p.property] = lengthAt i.castSucc.succ false
        unfold lengthAt
        rw [flipWedge, ite_eq_left rfl]
        exact first_len.symm
      · change BankLength[q.val,q.property] = lengthAt i.castSucc.succ true
        unfold lengthAt
        rw [flipWedge, ite_eq_right (Bool.noConfusion : true ≠ false)]
        exact last_len.symm
    have original := L.contourRoofWedge_markedSectorGerm S p q (A.visit i)
      (A.previous_returns old_child rfl i) (A.following_enters new_child rfl i) nonroot
    have germ : Nonempty (MarkedSectorGerm (Map ((D).vertexPoint Retain
        ((D).boundaryEndVertex Retain (S.contour.cycle.point (A.visit i))))) (wedge i) mark speed) :=
      original
    refine ⟨mark, lens ▸ ((angleWedge i).symm ▸ germ), ?_, ?_⟩
    · intro t
      rw [flipWedge]
      exact (atWedgeRight i t).1
    · intro t
      rw [flipWedge]
      exact (atWedgeLeft i t).1
  have all_sectors (i : Fin (n + 3)) : SectorAt i (H.center i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact old_center.symm ▸ old_local
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · exact new_center.symm ▸ new_local
      · exact (roof_center k).symm ▸ roof_local k
  choose marks charts before after using all_sectors
  let heading : Fin (n + 4) → ℝ := Fin.partialSum angle
  have difference (i : Fin (n + 3)) : heading i.succ - heading i.castSucc = angle i := by
    change Fin.partialSum angle i.succ - _ = _
    rw [Fin.partialSum_succ]
    ring
  have angle_pos (i : Fin (n + 3)) : 0 < angle i :=
    (Classical.choice (charts i)).sector.angle_pos
  have ordered_heading : StrictMono heading := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    apply sub_pos.mp
    rw [difference]
    exact angle_pos i
  have full_heading : heading (Fin.last (n + 3)) = 2 * Real.pi := by
    suffices heading (Fin.last (n + 3)) = ∑ i, angle i from this.trans full
    change ((List.ofFn angle).take (n + 3)).sum = _
    rw [List.take_of_length_le (by simp)]
    exact List.sum_ofFn
  have small (i : Fin (n + 3)) : heading i.succ - heading i.castSucc < 2 * Real.pi := by
    rw [difference]
    obtain ⟨j, different⟩ := exists_ne i
    have positive : 0 < ∑ k ∈ Finset.univ.erase i, angle k :=
      Finset.sum_pos (fun k _ => angle_pos k)
        ⟨j, Finset.mem_erase.mpr ⟨different, Finset.mem_univ _⟩⟩
    have total := (Finset.sum_erase_add _ angle (Finset.mem_univ i)).trans full
    linarith
  let atlas : MetricGluing.BankStackCyclicClass.MarkedAtlas Pieces Stack Base Gap H := {
    heading := heading
    ordered := ordered_heading
    start := Fin.partialSum_zero angle
    finish := full_heading
    width := small
    parameterize := parameterize
    at_zero := at_zero
    length := len
    length_pos := len_pos
    metric := metric
    reflected := flip
    mark := marks
    before := fun i t =>
      (congrArg (slotEnd (H.side i)) (time_at i t)).trans (before i t)
    after := fun i t => by
      have h := after (advance i) t
      change endpoint (!(H.side (previous (advance i)))) (previous (advance i)) t = _ at h
      have eq : previous (advance i) = i := advance.symm_apply_apply i
      rw [eq] at h
      exact (congrArg (slotEnd (!(H.side i))) (time_at i t)).trans h
    germ := fun i => (difference i).symm ▸ Classical.choice (charts i)
  }
  obtain ⟨ε, εpos, cover⟩ := L.contourGraft_piece_ball_cover S
    (H.center 0)
  have native := atlas.hasMetricBallChart unique
    (L.isClosedEmbedding_contourBaseMark S)
    (isClosedEmbedding_contourGapMark S)
    εpos cover
  exact ⟨slot, new_out, old_out, first_center ▸ native⟩

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
