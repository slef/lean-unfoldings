module

public import Unfoldings.FewestNets.ThreeExitGraftSingleTipClass
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

local instance graftSingleTipBallIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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

private def timedSlot (s : NamedSlot) (t : unitInterval) : Time :=
  ⟨⟨FiniteBank[s.1.val,s.1.property], s.2.1⟩, finiteSlotParameterize s.2.2 t⟩

set_option maxHeartbeats 4200000 in
-- The source tip and every distinct roof copy retain their exact incident slot parameters.
/-- An original source with no positive descendant gives a whole chart at its actual gap tip. -/
theorem contourGraftSingleTip_planarBall (event : Event)
    (only : Stack SourceEdge[event] = [event]) :
    HasMetricBallChart ℂ (Point ⟨some event, (models event).edgePoint false 0 0⟩) := by
  let (a : Attachment) : TopologicalSpace (Param a) :=
    (contourAttachmentMetric S a).toUniformSpace.toTopologicalSpace
  let parent : Edge := ⟨SourceOf[event],SourceOfNonroot[event]⟩
  let b := SourceEdge[event]
  let A := (D).contourFullParentWedgeRun Selection S.contour (Fcut).boundary_roots S.starts parent
  obtain ⟨H, first_center, roof_center, route, flags, empty, distinct⟩ :=
    L.exists_contourGraftSingleSourceTipClass S event
      (geometry event) only
  let n := A.length
  let last := (Fin.last n).succ
  let firstSlot : NamedSlot := ⟨parent, Fin.last (Stack b).length, false⟩
  let finalSlot : NamedSlot := ⟨parent, 0, false⟩
  let middle (j : Fin n) : NamedSlot := ⟨A.child j, 0, true⟩
  let schedule (i : Fin (n + 2)) : NamedSlot :=
    Fin.cases firstSlot (Fin.lastCases finalSlot middle) i
  let time (i : Fin (n + 2)) := timedSlot S (schedule i)
  have slot_last : schedule last = finalSlot := by
    change Fin.lastCases finalSlot middle (Fin.last n) = finalSlot
    exact Fin.lastCases_last
  have slot_inner (i : Fin n) : schedule i.castSucc.succ = middle i := by
    change Fin.lastCases finalSlot middle i.castSucc = middle i
    exact Fin.lastCases_castSucc i
  have time_zero (t : unitInterval) : time 0 t = ⟨⟨b, Fin.last (Stack b).length⟩, t⟩ := rfl
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
    · rw [MetricGluing.BankStackCyclicClass.singleTime_zero, time_zero]
      rfl
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · rw [MetricGluing.BankStackCyclicClass.singleTime_last, time_last]
        rfl
      · rw [MetricGluing.BankStackCyclicClass.singleTime_between, time_inner,
          unitInterval.symm_zero]
  obtain ⟨parameterize, actual_time, at_zero, metric⟩ :=
    L.contourGraftCyclicFiniteSlots_trace_parameters S H schedule origin
  let lengthOf (s : NamedSlot) := BankLength[s.1.val,s.1.property]
  let len (i : Fin (n + 2)) := lengthOf (schedule i)
  have len_pos (i : Fin (n + 2)) : 0 < len i := (D).boundaryBankLength_pos _
  have len_zero : len 0 = BankLength[parent.val,parent.property] := rfl
  have len_last : len last = BankLength[parent.val,parent.property] := by
    change lengthOf (schedule last) = lengthOf finalSlot
    rw [slot_last]
  have len_inner (i : Fin n) :
      len i.castSucc.succ = BankLength[(A.child i).val,(A.child i).property] := by
    change lengthOf (schedule i.castSucc.succ) = lengthOf (middle i)
    rw [slot_inner]
  have member : event ∈ Stack b := only.symm ▸ List.mem_cons_self
  let eval (flag : Bool) (t : Time) := EndAt flag t.1 t.2
  let pointAt (flag : Bool) (i : Fin (n + 2)) (t : unitInterval) := eval flag (time i t)
  have entry_mark (t : unitInterval) :
      pointAt false 0 t = ⟨some event, Gap b event member true t⟩ ∧
      pointAt true 0 t = ⟨none, Base b true t⟩ := by
    have names := MetricGluing.bankStack_last_gap_addresses (Parameter := Param)
      Stack b t event [] only
    change eval false (time 0 t) = _ ∧ eval true (time 0 t) = _
    rw [time_zero]
    exact ⟨MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap false _
      b event member true t names.1, MetricGluing.bankStackEndpoint_eq_of_base_address
      Stack Pieces Base Gap true _ b true t names.2⟩
  have exit_mark (t : unitInterval) : pointAt false last t = ⟨none, Base b false t⟩ ∧
      pointAt true last t = ⟨some event, Gap b event member false t⟩ := by
    have names := MetricGluing.bankStack_first_gap_addresses (Parameter := Param)
      Stack b t event [] only
    change eval false (time last t) = _ ∧ eval true (time last t) = _
    rw [time_last]
    exact ⟨MetricGluing.bankStackEndpoint_eq_of_base_address Stack Pieces Base Gap false _
      b false t names.1, MetricGluing.bankStackEndpoint_eq_of_gap_address
      Stack Pieces Base Gap true _ b event member false t names.2⟩
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
  have flag_last : H.side last = false := by
    rw [flags, MetricGluing.BankStackCyclicClass.singleSideWith_last]
  let entering (i : Fin (n + 2)) (t : unitInterval) := pointAt (!(H.side (prev i))) (prev i) t
  let leaving (i : Fin (n + 2)) (t : unitInterval) := pointAt (H.side i) i t
  let defect := (D).interiorAngularDefect Set.univ parent.val
  let wedge (i : Fin (n + 1)) := (D).totalAngle Retain
    ((D).boundaryEndVertex Retain (S.contour.cycle.point (A.visit i)))
  let angle (i : Fin (n + 2)) : ℝ := Fin.cases defect wedge i
  have sum : (∑ i, wedge i) = (D).totalAngle Set.univ parent.val :=
    (D).contourFullParentWedgeRun_sum Selection S.contour (Fcut).boundary_roots S.starts parent
  have κ : 0 < defect := event.property.2
  have total : ∑ i, angle i = 2 * Real.pi := by
    rw [Fin.sum_univ_succ]
    change defect + (∑ i, wedge i) = _
    rw [sum]
    have interior : ¬ (D).IsBoundaryVertex Set.univ parent.val :=
      fun b => parent.property ((Fcut).boundary_roots b)
    change (D).interiorAngularDefect Set.univ parent.val + (D).totalAngle Set.univ parent.val = _
    rw [TriangleComplex.interiorAngularDefect, ite_eq_right interior]
    ring
  have small (i : Fin (n + 1)) : wedge i < 2 * Real.pi := by
    have pos (j : Fin (n + 1)) : 0 ≤ wedge j := ((D).totalAngle_pos Retain _).le
    have le : wedge i ≤ ∑ j, wedge j := Finset.single_le_sum
      (fun j _ => pos j) (Finset.mem_univ i)
    have full := total
    rw [Fin.sum_univ_succ] at full
    change defect + (∑ i, wedge i) = 2 * Real.pi at full
    linarith
  let flip (i : Fin (n + 2)) := decide (i = 0)
  have flip_zero : flip 0 = true := by simp [flip]
  have flip_roof (i : Fin (n + 1)) : flip i.succ = false := by simp [flip]
  let lengthAt (i : Fin (n + 2)) (u : Bool) : ℝ := if u = flip i then len (prev i) else len i
  let Sector (i : Fin (n + 2)) (c : MetricGluing.Total Pieces) :=
    ∃ mark : Bool → unitInterval → Pieces c.1,
      Nonempty (MarkedSectorGerm c.2 (angle i) mark (lengthAt i)) ∧
      (∀ t, leaving i t = ⟨c.1, mark (!(flip i)) t⟩) ∧
      ∀ t, entering i t = ⟨c.1, mark (flip i) t⟩
  have tip_sector : Sector 0 ⟨some event, (models event).edgePoint false 0 0⟩ := by
    let mark (u : Bool) (t : unitInterval) := Gap b event member (!u) t
    let speed (_ : Bool) := BankLength[parent.val,parent.property]
    have germ : Nonempty (MarkedSectorGerm ((models event).edgePoint false 0 0)
        (angle 0) mark speed) :=
      L.contourGraftTip_markedSectorGerm S event member
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
      exact (exit_mark t).2
  let p := contourGraftRoofRunIncoming S A (parent, true, false)
  let q := contourGraftRoofRunOutgoing S A (parent, false, false)
  let speed (e : Edge) := BankLength[e.val,e.property]
  let markSite (s : Edge × Bool × Bool) (t : unitInterval) : MetricGluing.Total Pieces :=
    ⟨none, Base (.inl s.1) s.2.1 (finiteSlotParameterize s.2.2 t)⟩
  have marksLeft (i : Fin (n + 1)) (t : unitInterval) :
      entering i.succ t = markSite (p i) t ∧ len (prev i.succ) = speed (p i).1 := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change pointAt (!(H.side (prev (0 : Fin (n + 1)).succ)))
        (prev (0 : Fin (n + 1)).succ) t = _ ∧ _
      rw [prev_first, flag_zero]
      exact ⟨(entry_mark t).2, len_zero⟩
    · change pointAt (!(H.side (prev j.succ.succ))) (prev j.succ.succ) t = _ ∧ _
      rw [prev_succ, flag_inner]
      exact ⟨(inner_mark j t).1, len_inner j⟩
  have marksRight (i : Fin (n + 1)) (t : unitInterval) :
      leaving i.succ t = markSite (q i) t ∧ len i.succ = speed (q i).1 := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change pointAt (H.side last) last t = _ ∧ len last = _
      have label : q (Fin.last n) = (parent, false, false) := by
        change Fin.lastCases (motive := fun _ => Edge × Bool × Bool)
          (parent, false, false) (fun j => (A.child j, true, true)) (Fin.last n) = _
        exact Fin.lastCases_last
      rw [label, flag_last]
      exact ⟨(exit_mark t).1, len_last⟩
    · change pointAt (H.side j.castSucc.succ) j.castSucc.succ t = _ ∧ len j.castSucc.succ = _
      have label : q j.castSucc = (A.child j, true, true) := by
        change Fin.lastCases (motive := fun _ => Edge × Bool × Bool)
          (parent, false, false) (fun j => (A.child j, true, true)) j.castSucc = _
        exact Fin.lastCases_castSucc j
      rw [label, flag_inner]
      exact ⟨(inner_mark j t).2, len_inner j⟩
  have first_germ : Germ parent true false = (D).boundaryMate Retain (S.contour.cycle.point (A.visit 0)) := by
    have root := ((D).contourParent_firstVisit_germ Selection S.contour (Fcut).boundary_roots
      S.starts parent.val parent.property).symm
    exact root.trans (congrArg (fun j => (D).boundaryMate Retain (S.contour.cycle.point j))
      A.at_first.symm)
  have last_germ : Germ parent false false = S.contour.cycle.point (A.visit (Fin.last n)) :=
    ((D).contourParent_lastVisit_germ Selection S.contour (Fcut).boundary_roots
      S.starts parent.val parent.property).symm.trans (congrArg S.contour.cycle.point A.at_last.symm)
  obtain ⟨germs, _⟩ := L.contourGraftRoofRun_endpoints S parent A
    (parent, true, false) (parent, false, false) first_germ last_germ
  have roof_sector (i : Fin (n + 1)) : Sector i.succ RoofPoint[A.visit i] := by
    let left := p i
    let right := q i
    let mark (u : Bool) (t : unitInterval) := if u then
      Base (.inl right.1) right.2.1 (finiteSlotParameterize right.2.2 t)
      else Base (.inl left.1) left.2.1 (finiteSlotParameterize left.2.2 t)
    let length (u : Bool) := if u then speed right.1 else speed left.1
    have lens : length = lengthAt i.succ := by
      funext u
      cases u
      · change speed left.1 = lengthAt i.succ false
        unfold lengthAt
        rw [flip_roof, ite_eq_left rfl]
        exact (marksLeft i 0).2.symm
      · change speed right.1 = lengthAt i.succ true
        unfold lengthAt
        rw [flip_roof, ite_eq_right (Bool.noConfusion : true ≠ false)]
        exact (marksRight i 0).2.symm
    have nonroot : (D).contourOriginalVertex Selection S.contour (A.visit i) ∉ (Fcut).parents.roots :=
      (A.at_visit i).1.symm ▸ parent.property
    have original := L.contourRoofVertex_markedSectorGerm_of_germs S
      left.1 right.1 left.2.1 right.2.1 left.2.2 right.2.2 (A.visit i)
      (germs i).1 (germs i).2 nonroot (small i)
    have germ : Nonempty (MarkedSectorGerm (Map ((D).vertexPoint Retain
        ((D).boundaryEndVertex Retain (S.contour.cycle.point (A.visit i)))))
        (angle i.succ) mark length) := original
    refine ⟨mark, lens ▸ germ, ?_, ?_⟩
    · intro t
      rw [flip_roof]
      exact (marksRight i t).1
    · intro t
      rw [flip_roof]
      exact (marksLeft i t).1
  have all_sectors (i : Fin (n + 2)) : Sector i (H.center i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact first_center.symm ▸ tip_sector
    · exact (roof_center j).symm ▸ roof_sector j
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
