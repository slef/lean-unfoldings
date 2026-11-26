module

public import Unfoldings.FewestNets.ThreeExitGraftLastChildClass
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

local instance graftLastChildBallIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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

set_option maxHeartbeats 4000000 in
-- The original incident slot times and sector traces are all transported through one class.
/-- The actual outgoing exit-side class of the last child block is planar. -/
theorem contourGraftLastChild_planarBall
    (parent child : Edge) (at_parent : (Fcut).parents.parent child.val = parent.val)
    (event : Event) (inside : (Fcut).parents.Ancestor SourceOf[event] child.val)
    (older : List Event) (head : Stack FiniteBank[parent.val,parent.property] = event :: older)
    (strict : ∀ k : Fin LengthAt[event], let B := BankAt[event]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ)) :
    HasMetricBallChart ℂ (Point (EndAt true ⟨FiniteBank[parent.val,parent.property], 0⟩ 0)) := by
  let (a : Attachment) : TopologicalSpace (Param a) :=
    (contourAttachmentMetric S a).toUniformSpace.toTopologicalSpace
  obtain ⟨A, H, first_center, roof_center, route, flags, empty, ⟨rest, child_head⟩, distinct⟩ :=
    L.exists_contourGraftLastChildClass S parent child at_parent
      event inside (geometry event) older head
  let n := A.length
  let a := FiniteBank[child.val,child.property]
  let b := FiniteBank[parent.val,parent.property]
  let last := (Fin.last n).succ
  let schedule (i : Fin (n + 2)) : NamedSlot :=
    Fin.cases ⟨child, 0, true⟩ (Fin.lastCases ⟨parent, 0, false⟩
      (fun j => ⟨A.child j, 0, true⟩)) i
  let time (i : Fin (n + 2)) := timedSlot S (schedule i)
  have slot_last : schedule last = ⟨parent, 0, false⟩ := by
    change Fin.lastCases (motive := fun _ => NamedSlot) ⟨parent, 0, false⟩
      (fun j => ⟨A.child j, 0, true⟩) (Fin.last n) = _
    exact Fin.lastCases_last
  have slot_inner (i : Fin n) : schedule i.castSucc.succ = ⟨A.child i, 0, true⟩ := by
    change Fin.lastCases (motive := fun _ => NamedSlot) ⟨parent, 0, false⟩
      (fun j => ⟨A.child j, 0, true⟩) i.castSucc = _
    exact Fin.lastCases_castSucc i
  have time_zero (t : unitInterval) : time 0 t = ⟨⟨a, 0⟩, unitInterval.symm t⟩ := rfl
  have time_last (t : unitInterval) : time last t = ⟨⟨b, 0⟩, t⟩ := by
    change timedSlot S (schedule last) t = _
    rw [slot_last]
    rfl
  have time_inner (i : Fin n) (t : unitInterval) : time i.castSucc.succ t =
      ⟨⟨FiniteBank[(A.child i).val,(A.child i).property], 0⟩, unitInterval.symm t⟩ := by
    change timedSlot S (schedule i.castSucc.succ) t = _
    rw [slot_inner]
    rfl
  have origin (i : Fin (n + 2)) : H.time i = time i 0 := by
    rw [route]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [MetricGluing.BankStackCyclicClass.singleTime_zero, time_zero, unitInterval.symm_zero]
    · refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [MetricGluing.BankStackCyclicClass.singleTime_last, time_last]
      · rw [MetricGluing.BankStackCyclicClass.singleTime_between, time_inner,
          unitInterval.symm_zero]
  obtain ⟨parameterize, actual_time, at_zero, metric⟩ :=
    L.contourGraftCyclicFiniteSlots_trace_parameters S H schedule origin
  let lengthOf (s : NamedSlot) := BankLength[s.1.val,s.1.property]
  let len (i : Fin (n + 2)) := lengthOf (schedule i)
  have len_pos (i : Fin (n + 2)) : 0 < len i := (D).boundaryBankLength_pos _
  have len_zero : len 0 = BankLength[child.val,child.property] := rfl
  have len_last : len last = BankLength[parent.val,parent.property] := by
    change lengthOf (schedule last) = lengthOf ⟨parent, 0, false⟩
    rw [slot_last]
  have len_inner (i : Fin n) :
      len i.castSucc.succ = BankLength[(A.child i).val,(A.child i).property] := by
    change lengthOf (schedule i.castSucc.succ) = lengthOf ⟨A.child i, 0, true⟩
    rw [slot_inner]
  have at_child : event ∈ Stack a := child_head.symm ▸ List.mem_cons_self
  have at_parent_stack : event ∈ Stack b := head.symm ▸ List.mem_cons_self
  let eval (flag : Bool) (t : Time) := EndAt flag t.1 t.2
  let pointAt (flag : Bool) (i : Fin (n + 2)) (t : unitInterval) := eval flag (time i t)
  have entry_mark (t : unitInterval) :
      pointAt false 0 t = ⟨none, Base a false (unitInterval.symm t)⟩ ∧
      pointAt true 0 t = ⟨some event, Gap a event at_child false (unitInterval.symm t)⟩ := by
    have names := MetricGluing.bankStack_first_gap_addresses (Parameter := Param)
      Stack a (unitInterval.symm t) event rest child_head
    change eval false (time 0 t) = _ ∧ eval true (time 0 t) = _
    rw [time_zero]
    exact ⟨MetricGluing.bankStackEndpoint_eq_of_base_address Stack Pieces Base Gap false _
      a false (unitInterval.symm t) names.1, MetricGluing.bankStackEndpoint_eq_of_gap_address
      Stack Pieces Base Gap true _ a event at_child false (unitInterval.symm t) names.2⟩
  have exit_mark (t : unitInterval) : pointAt false last t = ⟨none, Base b false t⟩ ∧
      pointAt true last t = ⟨some event, Gap b event at_parent_stack false t⟩ := by
    have names := MetricGluing.bankStack_first_gap_addresses (Parameter := Param)
      Stack b t event older head
    change eval false (time last t) = _ ∧ eval true (time last t) = _
    rw [time_last]
    exact ⟨MetricGluing.bankStackEndpoint_eq_of_base_address Stack Pieces Base Gap false _
      b false t names.1, MetricGluing.bankStackEndpoint_eq_of_gap_address
      Stack Pieces Base Gap true _ b event at_parent_stack false t names.2⟩
  have inner_mark (i : Fin n) (t : unitInterval) :
      pointAt false i.castSucc.succ t =
        ⟨none, Base (.inl (A.child i)) false (unitInterval.symm t)⟩ ∧
      pointAt true i.castSucc.succ t =
        ⟨none, Base (.inl (A.child i)) true (unitInterval.symm t)⟩ := by
    let c := FiniteBank[(A.child i).val,(A.child i).property]
    have names := MetricGluing.bankStack_empty_addresses (Parameter := Param)
      Stack c (unitInterval.symm t) (empty i)
    change eval false (time i.castSucc.succ t) = _ ∧ eval true (time i.castSucc.succ t) = _
    rw [time_inner]
    exact ⟨MetricGluing.bankStackEndpoint_eq_of_base_address Stack Pieces Base Gap false _
      c false (unitInterval.symm t) names.1, MetricGluing.bankStackEndpoint_eq_of_base_address
      Stack Pieces Base Gap true _ c true (unitInterval.symm t) names.2⟩
  let rotate := finRotate (n + 2)
  let prev := rotate.symm
  have prev_zero : prev 0 = last :=
    rotate.symm_apply_eq.mpr (((congrArg rotate (Fin.succ_last n)).trans finRotate_last).symm)
  have prev_first : prev (0 : Fin (n + 1)).succ = 0 :=
    rotate.symm_apply_eq.mpr (finRotate_of_lt (Nat.zero_lt_succ n)).symm
  have prev_succ (i : Fin n) : prev i.succ.succ = i.castSucc.succ :=
    rotate.symm_apply_eq.mpr (finRotate_of_lt (Nat.succ_lt_succ i.isLt)).symm
  have flag_zero : H.side 0 = true := by
    rw [flags, MetricGluing.BankStackCyclicClass.singleSide_zero]
  have flag_inner (i : Fin n) : H.side i.castSucc.succ = true := by
    rw [flags, MetricGluing.BankStackCyclicClass.singleSide_between]
  have flag_last : H.side last = false := by
    rw [flags, MetricGluing.BankStackCyclicClass.singleSide_last]
  let entering (i : Fin (n + 2)) (t : unitInterval) := pointAt (!(H.side (prev i))) (prev i) t
  let leaving (i : Fin (n + 2)) (t : unitInterval) := pointAt (H.side i) i t
  have roof_left (i : Fin (n + 1)) (t : unitInterval) :
      entering i.succ t = ⟨none, Base (.inl (A.previous child i)) false (unitInterval.symm t)⟩ ∧
        len (prev i.succ) = BankLength[(A.previous child i).val,(A.previous child i).property] := by
    refine Fin.cases ?_ (fun k => ?_) i
    · change pointAt (!(H.side (prev (0 : Fin (n + 1)).succ)))
        (prev (0 : Fin (n + 1)).succ) t = _ ∧ _
      rw [prev_first, flag_zero]
      exact ⟨(entry_mark t).1, len_zero⟩
    · change pointAt (!(H.side (prev k.succ.succ))) (prev k.succ.succ) t = _ ∧ _
      rw [prev_succ, flag_inner]
      exact ⟨(inner_mark k t).1, len_inner k⟩
  let saved := AngleAt[event,IndexAt[parent.val,parent.property,event,at_parent_stack]]
  let bend := 2 * Real.pi - saved
  let wedge (i : Fin (n + 1)) := (D).totalAngle Retain
    ((D).boundaryEndVertex Retain (S.contour.cycle.point (A.visit i)))
  let angle (i : Fin (n + 2)) : ℝ := Fin.cases bend wedge i
  have total : ∑ i, angle i = 2 * Real.pi := by
    rw [Fin.sum_univ_succ]
    exact (Fcut).contourGraftLastChild_angle_balance S.contour S.starts
      parent.val child.val parent.property child.property at_parent event inside at_parent_stack A
  let flip (i : Fin (n + 2)) := decide (i = 0)
  have flip_zero : flip 0 = true := by simp [flip]
  have flip_roof (i : Fin (n + 1)) : flip i.succ = false := by simp [flip]
  let lengthAt (i : Fin (n + 2)) (u : Bool) : ℝ := if u = flip i then len (prev i) else len i
  let Sector (i : Fin (n + 2)) (c : MetricGluing.Total Pieces) :=
    ∃ mark : Bool → unitInterval → Pieces c.1,
      Nonempty (MarkedSectorGerm c.2 (angle i) mark (lengthAt i)) ∧
      (∀ t, leaving i t = ⟨c.1, mark (!(flip i)) t⟩) ∧
      ∀ t, entering i t = ⟨c.1, mark (flip i) t⟩
  have gap_center : H.center 0 = ⟨some event, Gap b event at_parent_stack false 0⟩ := by
    have names := MetricGluing.bankStack_first_gap_addresses (Parameter := Param)
      Stack b 0 event older head
    exact first_center.trans (MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap
      true (⟨⟨b, 0⟩, 0⟩ : Time) b event at_parent_stack false 0 names.2)
  have gap_sector : Sector 0 ⟨some event, Gap b event at_parent_stack false 0⟩ := by
    let mark (u : Bool) (t : unitInterval) :=
      if u = false then Gap a event at_child false (unitInterval.symm t)
      else Gap b event at_parent_stack false t
    let speed (u : Bool) :=
      if u = false then BankLength[child.val,child.property]
      else BankLength[parent.val,parent.property]
    have original := marked_gap_at_parent L S child parent at_parent
      event at_child at_parent_stack strict false
    have germ : Nonempty (MarkedSectorGerm (Gap b event at_parent_stack false 0)
        (angle 0) mark speed) := by
      simpa only [angle, Fin.cases_zero, bend, saved, mark, speed, Bool.false_eq_true,
        ite_false] using original
    have lens : speed = lengthAt 0 := by
      funext u
      cases u <;> simp only [speed, lengthAt, flip_zero, len_zero, prev_zero, len_last,
        Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true]
    refine ⟨mark, lens ▸ germ, ?_, ?_⟩
    · intro t
      change pointAt (H.side 0) 0 t = _
      rw [flag_zero, flip_zero]
      exact (entry_mark t).2
    · intro t
      change pointAt (!(H.side (prev 0))) (prev 0) t = _
      rw [prev_zero, flag_last, flip_zero]
      exact (exit_mark t).2
  have small_wedge (i : Fin (n + 1)) : wedge i < 2 * Real.pi := by
    let data := Interval[child.val,child.property]
    let w := (D).boundaryEndVertex Retain (S.contour.cycle.point (A.visit i))
    let z := (D).boundaryEndVertex Retain (S.contour.cycle.point data.enter)
    let forget := (D).vertexForgetCuts (Set.subset_univ Retain)
    have entry := (D).contourParentInterval_entry_original Selection S.contour (Fcut).boundary_roots
      S.starts child.val child.property
    have offset := ((D).contourChild_consecutive_parent_visits Selection S.contour
      (Fcut).boundary_roots S.starts child.val child.property
      (at_parent.symm ▸ parent.property)).1
    change (finRotate (S.contour.length + 1) data.leave).val = data.leave.val + 1 at offset
    have rank := (A.at_visit i).2.1
    change (finRotate (S.contour.length + 1) data.leave).val ≤ (A.visit i).val at rank
    have other : w ≠ z := by
      intro same
      have eq := (D).boundaryCycle_vertices_injective Retain S.contour.cycle S.contour.closes same
      have named := congrArg Fin.val eq
      have ordered := data.ordered
      omega
    have same : forget z = forget w := entry.1.trans (at_parent.trans (A.at_visit i).1.symm)
    have interior : ¬ (D).IsBoundaryVertex Set.univ (forget w) := fun bound =>
      parent.property ((A.at_visit i).1 ▸ ((Fcut).boundary_roots bound))
    exact ((D).totalAngle_lt_forgetCuts_of_other_copy (Set.subset_univ Retain) w z
      other same).trans_le ((Q).totalAngle_le_two_pi _ interior)
  have roof_sector (i : Fin (n + 1)) (q : Edge) (side finish : Bool)
      (right : Germ q side finish = S.contour.cycle.point (A.visit i))
      (right_mark : ∀ t : unitInterval,
        leaving i.succ t = ⟨none, Base (.inl q) side (finiteSlotParameterize finish t)⟩)
      (right_length : len i.succ = BankLength[q.val,q.property]) :
      Sector i.succ RoofPoint[A.visit i] := by
    let p := A.previous child i
    let mark (u : Bool) (t : unitInterval) := if u then
      Base (.inl q) side (finiteSlotParameterize finish t)
      else Base (.inl p) false (unitInterval.symm t)
    let speed (u : Bool) := if u then BankLength[q.val,q.property] else BankLength[p.val,p.property]
    have left : Germ p false true = (D).boundaryMate Retain (S.contour.cycle.point (A.visit i)) := by
      have step := (S.contour.next_cyclic (D) (Interval[p.val,p.property]).leave).trans
        (congrArg S.contour.cycle.point (A.previous_returns child rfl i))
      exact ((D).boundaryMate_involutive Retain _).symm.trans
        (congrArg ((D).boundaryMate Retain) step)
    have nonroot : (D).contourOriginalVertex Selection S.contour (A.visit i) ∉ (Fcut).parents.roots :=
      (A.at_visit i).1.symm ▸ parent.property
    have original := L.contourRoofVertex_markedSectorGerm_of_germs S
      p q false side true finish (A.visit i) left right nonroot (small_wedge i)
    have lens : speed = lengthAt i.succ := by
      funext u
      cases u
      · change BankLength[p.val,p.property] = lengthAt i.succ false
        unfold lengthAt
        rw [flip_roof, ite_eq_left rfl]
        exact (roof_left i 0).2.symm
      · change BankLength[q.val,q.property] = lengthAt i.succ true
        unfold lengthAt
        rw [flip_roof, ite_eq_right (Bool.noConfusion : true ≠ false)]
        exact right_length.symm
    have germ : Nonempty (MarkedSectorGerm (Map ((D).vertexPoint Retain
        ((D).boundaryEndVertex Retain (S.contour.cycle.point (A.visit i)))))
        (angle i.succ) mark speed) := original
    refine ⟨mark, lens ▸ germ, ?_, ?_⟩
    · intro t
      rw [flip_roof]
      exact right_mark t
    · intro t
      rw [flip_roof]
      exact (roof_left i t).1
  have all_sectors (i : Fin (n + 2)) : Sector i (H.center i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact gap_center.symm ▸ gap_sector
    · rw [roof_center]
      refine Fin.lastCases ?_ (fun i => ?_) j
      · apply roof_sector (Fin.last n) parent false false
        · rw [A.at_last]
          rfl
        · intro t
          change pointAt (H.side last) last t = _
          rw [flag_last]
          exact (exit_mark t).1
        · exact len_last
      · apply roof_sector i.castSucc (A.child i) true true
        · change (D).boundaryTurn Retain ((D).boundaryTurn Retain
            (S.contour.cycle.point (Interval[(A.child i).val,(A.child i).property]).enter)) = _
          exact ((D).boundaryTurn_involutive Retain _).trans
            (congrArg S.contour.cycle.point (A.enters i))
        · intro t
          change pointAt (H.side i.castSucc.succ) i.castSucc.succ t = _
          rw [flag_inner]
          exact (inner_mark i t).2
        · exact len_inner i
  let atlas := MetricGluing.BankStackCyclicClass.MarkedAtlas.ofGerms Pieces Stack Base Gap H
    angle total parameterize at_zero len len_pos metric flip (fun i => by
      obtain ⟨mark, germ, out, enter⟩ := all_sectors i
      refine ⟨mark, germ, ?_, ?_⟩
      · intro t
        exact (congrArg (eval (H.side i)) (actual_time i t)).trans (out t)
      · intro t
        exact (congrArg (eval (!(H.side (prev i)))) (actual_time (prev i) t)).trans (enter t))
  obtain ⟨r, rpos, cover⟩ := L.contourGraft_piece_ball_cover S
    (H.center 0)
  have chart := atlas.hasMetricBallChart distinct
    (L.isClosedEmbedding_contourBaseMark S)
    (isClosedEmbedding_contourGapMark S) rpos cover
  exact first_center ▸ chart

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
