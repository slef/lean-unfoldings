module

public import Unfoldings.FewestNets.ThreeExitGraftFirstChildClass
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

local instance graftFirstChildBallIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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
/-- The actual outgoing entry-side class of a flat parent is planar. -/
theorem contourGraftFirstChild_planarBall
    (parent child : Edge) (at_parent : (Fcut).parents.parent child.val = parent.val)
    (event : Event) (inside : (Fcut).parents.Ancestor SourceOf[event] child.val)
    (later : List Event) (oldest : Stack FiniteBank[parent.val,parent.property] = later ++ [event])
    (flat : (D).interiorAngularDefect Set.univ parent.val = 0)
    (strict : ∀ k : Fin LengthAt[event], let B := BankAt[event]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ)) :
    let b := FiniteBank[parent.val,parent.property]
    HasMetricBallChart ℂ (Point (EndAt false ⟨b, Fin.last (Stack b).length⟩ 0)) := by
  let (a : Attachment) : TopologicalSpace (Param a) :=
    (contourAttachmentMetric S a).toUniformSpace.toTopologicalSpace
  obtain ⟨A, H, first_center, roof_center, route, flags, empty, ⟨rest, child_end⟩, distinct⟩ :=
    L.exists_contourGraftFirstChildClass S parent child at_parent
      event inside (geometry event) later oldest
  let n := A.length
  let a := FiniteBank[child.val,child.property]
  let b := FiniteBank[parent.val,parent.property]
  let last := (Fin.last n).succ
  let rootSlot : NamedSlot := ⟨parent, Fin.last (Stack b).length, false⟩
  let childSlot : NamedSlot := ⟨child, Fin.last (Stack a).length, true⟩
  let mid (i : Fin n) : NamedSlot := ⟨A.child i, 0, true⟩
  let schedule (i : Fin (n + 2)) : NamedSlot :=
    Fin.cases rootSlot (Fin.lastCases childSlot mid) i
  let time (i : Fin (n + 2)) := timedSlot S (schedule i)
  have slot_last : schedule last = childSlot := by
    change Fin.lastCases childSlot mid (Fin.last n) = childSlot
    exact Fin.lastCases_last
  have slot_inner (i : Fin n) : schedule i.castSucc.succ = mid i := by
    change Fin.lastCases childSlot mid i.castSucc = mid i
    exact Fin.lastCases_castSucc i
  have time_zero (t : unitInterval) : time 0 t = ⟨⟨b, Fin.last (Stack b).length⟩, t⟩ := rfl
  have time_last (t : unitInterval) :
      time last t = ⟨⟨a, Fin.last (Stack a).length⟩, unitInterval.symm t⟩ := by
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
    · rw [MetricGluing.BankStackCyclicClass.singleTime_zero, time_zero]
      rfl
    · refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [MetricGluing.BankStackCyclicClass.singleTime_last, time_last, unitInterval.symm_zero]
        rfl
      · rw [MetricGluing.BankStackCyclicClass.singleTime_between, time_inner,
          unitInterval.symm_zero]
  obtain ⟨parameterize, actual_time, at_zero, metric⟩ :=
    L.contourGraftCyclicFiniteSlots_trace_parameters S H schedule origin
  let lengthOf (s : NamedSlot) := BankLength[s.1.val,s.1.property]
  let len (i : Fin (n + 2)) := lengthOf (schedule i)
  have len_pos (i : Fin (n + 2)) : 0 < len i := (D).boundaryBankLength_pos _
  have len_zero : len 0 = BankLength[parent.val,parent.property] := rfl
  have len_last : len last = BankLength[child.val,child.property] := by
    change lengthOf (schedule last) = lengthOf childSlot
    rw [slot_last]
  have len_inner (i : Fin n) :
      len i.castSucc.succ = BankLength[(A.child i).val,(A.child i).property] := by
    change lengthOf (schedule i.castSucc.succ) = lengthOf (mid i)
    rw [slot_inner]
  have at_child : event ∈ Stack a := child_end.symm ▸ List.mem_append_right rest List.mem_cons_self
  have at_parent_stack : event ∈ Stack b :=
    oldest.symm ▸ List.mem_append_right later List.mem_cons_self
  let eval (flag : Bool) (t : Time) := EndAt flag t.1 t.2
  let pointAt (flag : Bool) (i : Fin (n + 2)) (t : unitInterval) := eval flag (time i t)
  have entry_mark (t : unitInterval) :
      pointAt false 0 t = ⟨some event, Gap b event at_parent_stack true t⟩ ∧
      pointAt true 0 t = ⟨none, Base b true t⟩ := by
    have names := MetricGluing.bankStack_last_gap_addresses (Parameter := Param)
      Stack b t event later oldest
    change eval false (time 0 t) = _ ∧ eval true (time 0 t) = _
    rw [time_zero]
    exact ⟨MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap false _
      b event at_parent_stack true t names.1, MetricGluing.bankStackEndpoint_eq_of_base_address
      Stack Pieces Base Gap true _ b true t names.2⟩
  have exit_mark (t : unitInterval) :
      pointAt false last t = ⟨some event, Gap a event at_child true (unitInterval.symm t)⟩ ∧
      pointAt true last t = ⟨none, Base a true (unitInterval.symm t)⟩ := by
    have names := MetricGluing.bankStack_last_gap_addresses (Parameter := Param)
      Stack a (unitInterval.symm t) event rest child_end
    change eval false (time last t) = _ ∧ eval true (time last t) = _
    rw [time_last]
    exact ⟨MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap false _
      a event at_child true (unitInterval.symm t) names.1,
      MetricGluing.bankStackEndpoint_eq_of_base_address Stack Pieces Base Gap true _
        a true (unitInterval.symm t) names.2⟩
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
  have flag_zero : H.side 0 = false := by
    rw [flags, MetricGluing.BankStackCyclicClass.singleSideWith_zero]
  have flag_inner (i : Fin n) : H.side i.castSucc.succ = true := by
    rw [flags, MetricGluing.BankStackCyclicClass.singleSideWith_between]
  have flag_last : H.side last = true := by
    rw [flags, MetricGluing.BankStackCyclicClass.singleSideWith_last]
  let entering (i : Fin (n + 2)) (t : unitInterval) := pointAt (!(H.side (prev i))) (prev i) t
  let leaving (i : Fin (n + 2)) (t : unitInterval) := pointAt (H.side i) i t
  let saved := AngleAt[event,IndexAt[parent.val,parent.property,event,at_parent_stack]]
  let wedge (i : Fin (n + 1)) := (D).totalAngle Retain
    ((D).boundaryEndVertex Retain (S.contour.cycle.point (A.visit i)))
  let angle (i : Fin (n + 2)) : ℝ := Fin.cases saved wedge i
  have total : ∑ i, angle i = 2 * Real.pi := by
    rw [Fin.sum_univ_succ]
    have balance := (Fcut).contourGraftFirstChild_angle_balance S.contour S.starts
      parent.val child.val parent.property child.property at_parent event inside at_parent_stack A
    change saved + (∑ i, wedge i) + (D).interiorAngularDefect Set.univ parent.val = _ at balance
    rw [flat, add_zero] at balance
    exact balance
  let flip (i : Fin (n + 2)) := decide (i = 0)
  have flip_zero : flip 0 = true := by simp [flip]
  have flip_roof (i : Fin (n + 1)) : flip i.succ = false := by simp [flip]
  let lengthAt (i : Fin (n + 2)) (u : Bool) : ℝ := if u = flip i then len (prev i) else len i
  let Sector (i : Fin (n + 2)) (c : MetricGluing.Total Pieces) :=
    ∃ mark : Bool → unitInterval → Pieces c.1,
      Nonempty (MarkedSectorGerm c.2 (angle i) mark (lengthAt i)) ∧
      (∀ t, leaving i t = ⟨c.1, mark (!(flip i)) t⟩) ∧
      ∀ t, entering i t = ⟨c.1, mark (flip i) t⟩
  have gap_center : H.center 0 = ⟨some event, Gap b event at_parent_stack true 0⟩ :=
    first_center.trans (entry_mark 0).1
  have gap_sector : Sector 0 ⟨some event, Gap b event at_parent_stack true 0⟩ := by
    let mark (u : Bool) (t : unitInterval) :=
      if u then Gap a event at_child true (unitInterval.symm t)
      else Gap b event at_parent_stack true t
    let speed (u : Bool) :=
      if u then BankLength[child.val,child.property]
      else BankLength[parent.val,parent.property]
    have original := marked_gap_at_parent L S child parent at_parent
      event at_child at_parent_stack strict true
    have germ : Nonempty (MarkedSectorGerm (Gap b event at_parent_stack true 0)
        (angle 0) mark speed) := by
      simpa only [angle, Fin.cases_zero, saved, mark, speed, ite_true] using original
    have lens : speed = lengthAt 0 := by
      funext u
      cases u <;> simp only [speed, lengthAt, flip_zero, len_zero, prev_zero, len_last,
        Bool.false_eq_true, ite_false, ite_true]
    refine ⟨mark, lens ▸ germ, ?_, ?_⟩
    · intro t
      change pointAt (H.side 0) 0 t = _
      rw [flag_zero, flip_zero]
      exact (entry_mark t).1
    · intro t
      change pointAt (!(H.side (prev 0))) (prev 0) t = _
      rw [prev_zero, flag_last, flip_zero]
      exact (exit_mark t).1
  let right (i : Fin (n + 1)) := A.following child i
  let roofExit (e : Edge) (t : unitInterval) : MetricGluing.Total Pieces :=
    ⟨none, Base (.inl e) true (unitInterval.symm t)⟩
  let bankSize (e : Edge) := BankLength[e.val,e.property]
  have roof_right (i : Fin (n + 1)) (t : unitInterval) :
      leaving i.succ t = roofExit (right i) t ∧ len i.succ = bankSize (right i) := by
    refine Fin.lastCases ?_ (fun k => ?_) i
    · change pointAt (H.side last) last t = roofExit (right (Fin.last n)) t ∧
        len last = bankSize (right (Fin.last n))
      have name : right (Fin.last n) = child := A.following_last child
      rw [flag_last, name]
      exact ⟨(exit_mark t).2, len_last⟩
    · change pointAt (H.side k.castSucc.succ) k.castSucc.succ t =
        roofExit (right k.castSucc) t ∧ len k.castSucc.succ = bankSize (right k.castSucc)
      have name : right k.castSucc = A.child k := A.following_castSucc child k
      rw [flag_inner, name]
      exact ⟨(inner_mark k t).2, len_inner k⟩
  have small_wedge (i : Fin (n + 1)) : wedge i < 2 * Real.pi := by
    let data := Interval[child.val,child.property]
    let returned := finRotate (S.contour.length + 1) data.leave
    let w := (D).boundaryEndVertex Retain (S.contour.cycle.point (A.visit i))
    let z := (D).boundaryEndVertex Retain (S.contour.cycle.point returned)
    let forget := (D).vertexForgetCuts (Set.subset_univ Retain)
    have step := (D).contourChild_consecutive_parent_visits Selection S.contour (Fcut).boundary_roots
      S.starts child.val child.property (at_parent.symm ▸ parent.property)
    have offset : returned.val = data.leave.val + 1 := step.1
    have rank : (A.visit i).val ≤ data.enter.val := (A.at_visit i).2.2
    have other : w ≠ z := by
      intro same
      have eq := (D).boundaryCycle_vertices_injective Retain S.contour.cycle S.contour.closes same
      have named := congrArg Fin.val eq
      have ordered := data.ordered
      omega
    have same : forget z = forget w :=
      step.2.2.1.trans (at_parent.trans (A.at_visit i).1.symm)
    have interior : ¬ (D).IsBoundaryVertex Set.univ (forget w) := fun bound =>
      parent.property ((A.at_visit i).1 ▸ ((Fcut).boundary_roots bound))
    exact ((D).totalAngle_lt_forgetCuts_of_other_copy (Set.subset_univ Retain) w z
      other same).trans_le ((Q).totalAngle_le_two_pi _ interior)
  have roof_sector (i : Fin (n + 1)) (p : Edge) (side finish : Bool)
      (left : Germ p side finish = (D).boundaryMate Retain (S.contour.cycle.point (A.visit i)))
      (left_mark : ∀ t : unitInterval,
        entering i.succ t = ⟨none, Base (.inl p) side (finiteSlotParameterize finish t)⟩)
      (left_length : len (prev i.succ) = BankLength[p.val,p.property]) :
      Sector i.succ RoofPoint[A.visit i] := by
    let q := right i
    let mark (u : Bool) (t : unitInterval) := if u then
      Base (.inl q) true (unitInterval.symm t)
      else Base (.inl p) side (finiteSlotParameterize finish t)
    let speed (u : Bool) := if u then BankLength[q.val,q.property] else BankLength[p.val,p.property]
    have other : Germ q true true = S.contour.cycle.point (A.visit i) := by
      have at_entry := A.following_enters child rfl i
      change (D).boundaryTurn Retain ((D).boundaryTurn Retain
        (S.contour.cycle.point (Interval[q.val,q.property]).enter)) = _
      exact ((D).boundaryTurn_involutive Retain _).trans (congrArg S.contour.cycle.point at_entry)
    have nonroot : (D).contourOriginalVertex Selection S.contour (A.visit i) ∉ (Fcut).parents.roots :=
      (A.at_visit i).1.symm ▸ parent.property
    have original := L.contourRoofVertex_markedSectorGerm_of_germs S
      p q side true finish true (A.visit i) left other nonroot (small_wedge i)
    have lens : speed = lengthAt i.succ := by
      funext u
      cases u
      · change BankLength[p.val,p.property] = lengthAt i.succ false
        unfold lengthAt
        rw [flip_roof, ite_eq_left rfl]
        exact left_length.symm
      · change BankLength[q.val,q.property] = lengthAt i.succ true
        unfold lengthAt
        rw [flip_roof, ite_eq_right (Bool.noConfusion : true ≠ false)]
        exact (roof_right i 0).2.symm
    have germ : Nonempty (MarkedSectorGerm (Map ((D).vertexPoint Retain
        ((D).boundaryEndVertex Retain (S.contour.cycle.point (A.visit i)))))
        (angle i.succ) mark speed) := original
    refine ⟨mark, lens ▸ germ, ?_, ?_⟩
    · intro t
      rw [flip_roof]
      exact (roof_right i t).1
    · intro t
      rw [flip_roof]
      exact left_mark t
  have all_sectors (i : Fin (n + 2)) : Sector i (H.center i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact gap_center.symm ▸ gap_sector
    · rw [roof_center]
      refine Fin.cases ?_ (fun k => ?_) j
      · apply roof_sector 0 parent true false
        · rw [A.at_first]
          exact ((D).contourParent_firstVisit_germ Selection S.contour (Fcut).boundary_roots
            S.starts parent.val parent.property).symm
        · intro t
          change pointAt (!(H.side (prev (0 : Fin (n + 1)).succ)))
            (prev (0 : Fin (n + 1)).succ) t = _
          rw [prev_first, flag_zero]
          exact (entry_mark t).2
        · rw [prev_first]
          exact len_zero
      · apply roof_sector k.succ (A.child k) false true
        · let e := A.child k
          have step := (S.contour.next_cyclic (D) (Interval[e.val,e.property]).leave).trans
            (congrArg S.contour.cycle.point (A.returns k))
          exact ((D).boundaryMate_involutive Retain _).symm.trans
            (congrArg ((D).boundaryMate Retain) step)
        · intro t
          change pointAt (!(H.side (prev k.succ.succ))) (prev k.succ.succ) t = _
          rw [prev_succ, flag_inner]
          exact (inner_mark k t).1
        · rw [prev_succ]
          exact len_inner k
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
  exact Eq.mp (congrArg (fun z : MetricGluing.Total Pieces =>
    HasMetricBallChart ℂ (Point z)) first_center) chart

/-- If the oldest gap comes from a child, completeness of the S.contour implies
the parent is flat and gives its entry-side planar ball. -/
theorem contourGraftFirstChild_planarBall_of_complete_contour
    (ends : (D).contourOriginalVertex Selection S.contour (Fin.last S.contour.length) ∈
      (Fcut).parents.roots)
    (parent child : Edge) (at_parent : (Fcut).parents.parent child.val = parent.val)
    (event : Event) (inside : (Fcut).parents.Ancestor SourceOf[event] child.val)
    (later : List Event) (oldest : Stack FiniteBank[parent.val,parent.property] = later ++ [event])
    (strict : ∀ k : Fin LengthAt[event], let B := BankAt[event]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ)) :
    let b := FiniteBank[parent.val,parent.property]
    HasMetricBallChart ℂ (Point (EndAt false ⟨b, Fin.last (Stack b).length⟩ 0)) := by
  let b := FiniteBank[parent.val,parent.property]
  have final : (Stack b).getLast? = some event := by
    rw [oldest, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil event []),
      List.getLast?_singleton]
  have absent (e : Event) (last : ((D).contourSavedGapStack Selection S.contour parent.val).getLast? =
      some e) : SourceOf[e] ≠ parent.val := by
    have same : e = event := Option.some.inj (last.symm.trans final)
    subst e
    intro at_source
    exact (Fcut).parents.not_ancestor_parent_self child.property
      (at_parent.symm ▸ (at_source ▸ inside))
  have flat := (Fcut).contourGraft_defect_eq_zero_of_no_last_source S.contour S.starts ends parent.val
    parent.property absent
  exact L.contourGraftFirstChild_planarBall S parent child at_parent
    event inside later oldest flat strict

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
