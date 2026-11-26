module

public import Unfoldings.FewestNets.ThreeExitGraftEmptyStackClass
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

local instance graftEmptyStackBallIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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

private def timedSlot (s : NamedSlot) (t : unitInterval) : Time :=
  ⟨⟨FiniteBank[s.1.val,s.1.property], s.2.1⟩, finiteSlotParameterize s.2.2 t⟩

set_option maxHeartbeats 4400000 in
-- Both normalized boundary rays are retained for each of the distinct original roof copies.
/-- An empty stack with at least two original roof copies gives a genuine planar ball. -/
theorem contourGraftEmptyStack_multiple_planarBall
    (ends : (D).contourOriginalVertex Selection S.contour (Fin.last S.contour.length) ∈
      (Fcut).parents.roots)
    (parent : Edge) (none_added : Stack FiniteBank[parent.val,parent.property] = [])
    (many : 0 < ((D).contourFullParentWedgeRun Selection S.contour
      (Fcut).boundary_roots S.starts parent).length) :
    HasMetricBallChart ℂ (Point (EndAt true ⟨FiniteBank[parent.val,parent.property], 0⟩ 0)) := by
  let (a : Attachment) : TopologicalSpace (Param a) :=
    (contourAttachmentMetric S a).toUniformSpace.toTopologicalSpace
  let b := FiniteBank[parent.val,parent.property]
  let A := (D).contourFullParentWedgeRun Selection S.contour (Fcut).boundary_roots S.starts parent
  obtain ⟨H, first_center, roof_center, route, flags, empty, distinct⟩ :=
    L.exists_contourGraftEmptyStackClass S parent none_added
  let n := A.length
  let last := Fin.last n
  let finalSlot : NamedSlot := ⟨parent, 0, false⟩
  let middle (i : Fin n) : NamedSlot := ⟨A.child i, 0, true⟩
  let schedule (i : Fin (n + 1)) : NamedSlot := Fin.lastCases finalSlot middle i
  let time (i : Fin (n + 1)) := timedSlot S (schedule i)
  have slot_last : schedule last = finalSlot := by
    change Fin.lastCases finalSlot middle (Fin.last n) = finalSlot
    exact Fin.lastCases_last
  have slot_inner (i : Fin n) : schedule i.castSucc = middle i := by
    change Fin.lastCases finalSlot middle i.castSucc = middle i
    exact Fin.lastCases_castSucc i
  have time_last (t : unitInterval) : time last t = ⟨⟨b, 0⟩, t⟩ := by
    change timedSlot S (schedule last) t = _
    rw [slot_last]
    rfl
  have time_inner (i : Fin n) (t : unitInterval) : time i.castSucc t =
      ⟨⟨FiniteBank[(A.child i).val,(A.child i).property], 0⟩, unitInterval.symm t⟩ := by
    change timedSlot S (schedule i.castSucc) t = _
    rw [slot_inner]
    rfl
  have origin (i : Fin (n + 1)) : H.time i = time i 0 := by
    rw [route]
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [MetricGluing.BankStackCyclicClass.roofTime_last, time_last]
    · rw [MetricGluing.BankStackCyclicClass.roofTime_between, time_inner, unitInterval.symm_zero]
  obtain ⟨parameterize, actual_time, at_zero, metric⟩ :=
    L.contourGraftCyclicFiniteSlots_trace_parameters S H schedule origin
  let lengthOf (s : NamedSlot) := BankLength[s.1.val,s.1.property]
  let len (i : Fin (n + 1)) := lengthOf (schedule i)
  have len_pos (i : Fin (n + 1)) : 0 < len i := (D).boundaryBankLength_pos _
  have len_last : len last = BankLength[parent.val,parent.property] := by
    change lengthOf (schedule last) = lengthOf finalSlot
    rw [slot_last]
  have len_inner (i : Fin n) : len i.castSucc = BankLength[(A.child i).val,(A.child i).property] := by
    change lengthOf (schedule i.castSucc) = lengthOf (middle i)
    rw [slot_inner]
  let eval (flag : Bool) (t : Time) := EndAt flag t.1 t.2
  let pointAt (flag : Bool) (i : Fin (n + 1)) (t : unitInterval) := eval flag (time i t)
  have exit_mark (t : unitInterval) : pointAt false last t = ⟨none, Base b false t⟩ ∧
      pointAt true last t = ⟨none, Base b true t⟩ := by
    have names := MetricGluing.bankStack_empty_addresses (Parameter := Param)
      Stack b t none_added
    change eval false (time last t) = _ ∧ eval true (time last t) = _
    rw [time_last]
    exact ⟨MetricGluing.bankStackEndpoint_eq_of_base_address Stack Pieces Base Gap false _
      b false t names.1, MetricGluing.bankStackEndpoint_eq_of_base_address
      Stack Pieces Base Gap true _ b true t names.2⟩
  have inner_mark (i : Fin n) (t : unitInterval) :
      pointAt false i.castSucc t = ⟨none, Base (.inl (A.child i)) false (unitInterval.symm t)⟩ ∧
      pointAt true i.castSucc t = ⟨none, Base (.inl (A.child i)) true (unitInterval.symm t)⟩ := by
    let c := FiniteBank[(A.child i).val,(A.child i).property]
    have names := MetricGluing.bankStack_empty_addresses (Parameter := Param)
      Stack c (unitInterval.symm t) (empty i)
    change eval false (time i.castSucc t) = _ ∧ eval true (time i.castSucc t) = _
    rw [time_inner]
    exact ⟨MetricGluing.bankStackEndpoint_eq_of_base_address Stack Pieces Base Gap false _
      c false (unitInterval.symm t) names.1, MetricGluing.bankStackEndpoint_eq_of_base_address
      Stack Pieces Base Gap true _ c true (unitInterval.symm t) names.2⟩
  let rotate := finRotate (n + 1)
  let prev := rotate.symm
  have prev_zero : prev 0 = last := rotate.symm_apply_eq.mpr finRotate_last.symm
  have prev_succ (i : Fin n) : prev i.succ = i.castSucc :=
    rotate.symm_apply_eq.mpr (finRotate_of_lt i.isLt).symm
  have flag_inner (i : Fin n) : H.side i.castSucc = true := by
    rw [flags, MetricGluing.BankStackCyclicClass.roofSide_between]
  have flag_last : H.side last = false := by
    rw [flags, MetricGluing.BankStackCyclicClass.roofSide_last]
  let entering (i : Fin (n + 1)) (t : unitInterval) := pointAt (!(H.side (prev i))) (prev i) t
  let leaving (i : Fin (n + 1)) (t : unitInterval) := pointAt (H.side i) i t
  let p := contourGraftRoofRunIncoming S A (parent, true, false)
  let q := contourGraftRoofRunOutgoing S A (parent, false, false)
  let speed (e : Edge) := BankLength[e.val,e.property]
  let markSite (s : Edge × Bool × Bool) (t : unitInterval) : MetricGluing.Total Pieces :=
    ⟨none, Base (.inl s.1) s.2.1 (finiteSlotParameterize s.2.2 t)⟩
  have left_marks (i : Fin (n + 1)) (t : unitInterval) :
      entering i t = markSite (p i) t ∧ len (prev i) = speed (p i).1 := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change pointAt (!(H.side (prev 0))) (prev 0) t = _ ∧ _
      rw [prev_zero, flag_last]
      exact ⟨(exit_mark t).2, len_last⟩
    · change pointAt (!(H.side (prev j.succ))) (prev j.succ) t = _ ∧ _
      rw [prev_succ, flag_inner]
      exact ⟨(inner_mark j t).1, len_inner j⟩
  have right_marks (i : Fin (n + 1)) (t : unitInterval) :
      leaving i t = markSite (q i) t ∧ len i = speed (q i).1 := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change pointAt (H.side last) last t = _ ∧ _
      have label : q last = (parent, false, false) := by
        change Fin.lastCases (motive := fun _ => Edge × Bool × Bool)
          (parent, false, false) (fun j => (A.child j, true, true)) (Fin.last n) = _
        exact Fin.lastCases_last
      rw [flag_last, label]
      exact ⟨(exit_mark t).1, len_last⟩
    · change pointAt (H.side j.castSucc) j.castSucc t = _ ∧ _
      have label : q j.castSucc = (A.child j, true, true) := by
        change Fin.lastCases (motive := fun _ => Edge × Bool × Bool)
          (parent, false, false) (fun j => (A.child j, true, true)) j.castSucc = _
        exact Fin.lastCases_castSucc j
      rw [flag_inner, label]
      exact ⟨(inner_mark j t).2, len_inner j⟩
  have flat : (D).interiorAngularDefect Set.univ parent.val = 0 :=
    (Fcut).contourGraft_defect_eq_zero_of_no_last_source S.contour S.starts ends parent.val parent.property
      (fun e h => by
        change (Stack b).getLast? = some e at h
        rw [none_added] at h
        cases h)
  let wedge (i : Fin (n + 1)) := (D).totalAngle Retain
    ((D).boundaryEndVertex Retain (S.contour.cycle.point (A.visit i)))
  have total : (∑ i, wedge i) = 2 * Real.pi := by
    have all : (∑ i, wedge i) = (D).totalAngle Set.univ parent.val :=
      (D).contourFullParentWedgeRun_sum Selection S.contour (Fcut).boundary_roots S.starts parent
    have interior : ¬ (D).IsBoundaryVertex Set.univ parent.val :=
      fun h => parent.property ((Fcut).boundary_roots h)
    rw [TriangleComplex.interiorAngularDefect, ite_eq_right interior] at flat
    exact all.trans (sub_eq_zero.mp flat).symm
  let : Nontrivial (Fin (n + 1)) := ⟨⟨0, last, fun h => by
    have rank : 0 = n := congrArg Fin.val h
    exact (ne_of_gt many) rank.symm⟩⟩
  have small (i : Fin (n + 1)) : wedge i < 2 * Real.pi := by
    have positive (j : Fin (n + 1)) : 0 < wedge j := (D).totalAngle_pos Retain _
    obtain ⟨j, different⟩ := exists_ne i
    have rest : 0 < ∑ k ∈ Finset.univ.erase i, wedge k :=
      Finset.sum_pos (fun k _ => positive k)
        ⟨j, Finset.mem_erase.mpr ⟨different, Finset.mem_univ _⟩⟩
    have full := (Finset.sum_erase_add _ wedge (Finset.mem_univ i)).trans total
    linarith
  have first_germ : Germ parent true false = (D).boundaryMate Retain (S.contour.cycle.point (A.visit 0)) := by
    have root := ((D).contourParent_firstVisit_germ Selection S.contour (Fcut).boundary_roots
      S.starts parent.val parent.property).symm
    exact root.trans (congrArg (fun j => (D).boundaryMate Retain (S.contour.cycle.point j))
      A.at_first.symm)
  have last_germ : Germ parent false false = S.contour.cycle.point (A.visit last) :=
    ((D).contourParent_lastVisit_germ Selection S.contour (Fcut).boundary_roots
      S.starts parent.val parent.property).symm.trans (congrArg S.contour.cycle.point A.at_last.symm)
  obtain ⟨germs, _⟩ := L.contourGraftRoofRun_endpoints S parent A
    (parent, true, false) (parent, false, false) first_germ last_germ
  have sector (i : Fin (n + 1)) (c : MetricGluing.Total Pieces) (center : c = RoofPoint[A.visit i]) :
      ∃ mark : Bool → unitInterval → Pieces c.1,
        Nonempty (MarkedSectorGerm c.2 (wedge i) mark (fun u => if u = false then len (prev i) else len i)) ∧
        (∀ t, leaving i t = ⟨c.1, mark true t⟩) ∧ ∀ t, entering i t = ⟨c.1, mark false t⟩ := by
    subst c
    let left := p i
    let right := q i
    let mark (u : Bool) (t : unitInterval) := if u then
      Base (.inl right.1) right.2.1 (finiteSlotParameterize right.2.2 t)
      else Base (.inl left.1) left.2.1 (finiteSlotParameterize left.2.2 t)
    let length (u : Bool) := if u then speed right.1 else speed left.1
    let chartLength (u : Bool) := if u = false then len (prev i) else len i
    have lens : length = chartLength := by
      funext u
      cases u
      · change speed left.1 = chartLength false
        exact (left_marks i 0).2.symm
      · change speed right.1 = chartLength true
        exact (right_marks i 0).2.symm
    have nonroot : (D).contourOriginalVertex Selection S.contour (A.visit i) ∉ (Fcut).parents.roots :=
      (A.at_visit i).1.symm ▸ parent.property
    have original := L.contourRoofVertex_markedSectorGerm_of_germs S
      left.1 right.1 left.2.1 right.2.1 left.2.2 right.2.2 (A.visit i)
      (germs i).1 (germs i).2 nonroot (small i)
    have germ : Nonempty (MarkedSectorGerm (Map ((D).vertexPoint Retain
        ((D).boundaryEndVertex Retain (S.contour.cycle.point (A.visit i)))))
        (wedge i) mark length) := original
    refine ⟨mark, ?_, fun t => (right_marks i t).1, fun t => (left_marks i t).1⟩
    change Nonempty (MarkedSectorGerm _ _ _ chartLength)
    rw [← lens]
    exact germ
  let atlas := MetricGluing.BankStackCyclicClass.MarkedAtlas.ofGerms Pieces Stack Base Gap H
    wedge total parameterize at_zero len len_pos metric (fun _ => false) (fun i => by
      obtain ⟨mark, germ, out, enter⟩ := sector i (H.center i) (roof_center i)
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
