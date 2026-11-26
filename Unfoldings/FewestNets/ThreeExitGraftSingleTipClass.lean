module

public import Unfoldings.FewestNets.ThreeExitGraftRoofRun
public import Unfoldings.FewestNets.ThreeExitGraftTipIncidence
public import Unfoldings.Metric.BankStackSingleBendCycle


/-! Cyclic incidences when the outgoing stack contains only its own source. -/

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

local instance graftSingleTipClassIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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

set_option maxHeartbeats 2200000 in
-- The two source sides share the same intrinsic tip and have distinct original slot labels.
/-- If its outgoing stack contains only its own gap, the original source tip and all
the roof wedges are exactly one cyclic class, even with original empty child cuts. -/
theorem exists_contourGraftSingleSourceTipClass
    (event : Event) (g : OrientedBankGap BankAt[event] MovedAt[event])
    (only : Stack SourceEdge[event] = [event]) :
    let parent := ⟨SourceOf[event], SourceOfNonroot[event]⟩
    let A := (D).contourFullParentWedgeRun Selection S.contour (Fcut).boundary_roots S.starts parent
    let b := SourceEdge[event]
    let opening := RoofTime b true 0
    let closing := RoofTime b false 0
    ∃ H : MetricGluing.BankStackCyclicClass Pieces Stack Base Gap (A.length + 1),
      H.center 0 = ⟨some event, (models event).edgePoint false 0 0⟩ ∧
      (∀ i : Fin (A.length + 1), H.center i.succ = RoofPoint[A.visit i]) ∧
      H.time = MetricGluing.BankStackCyclicClass.singleTime opening closing
        (fun i => ⟨⟨FiniteBank[(A.child i).val,(A.child i).property], 0⟩, 1⟩) ∧
      H.side = MetricGluing.BankStackCyclicClass.singleSideWith false false ∧
      (∀ i, Stack FiniteBank[(A.child i).val,(A.child i).property] = []) ∧
      Function.Injective H.center := by
  let parent : Edge := ⟨SourceOf[event], SourceOfNonroot[event]⟩
  let A := (D).contourFullParentWedgeRun Selection S.contour (Fcut).boundary_roots S.starts parent
  let b := SourceEdge[event]
  let opening := RoofTime b true 0
  let closing := RoofTime b false 0
  let roof (i : Fin (A.length + 1)) := RoofPoint[A.visit i]
  let bank (e : Edge) := FiniteBank[e.val,e.property]
  let time (i : Fin A.length) : Time := ⟨⟨bank (A.child i), 0⟩, 1⟩
  let tip : MetricGluing.Total Pieces := ⟨some event, (models event).edgePoint false 0 0⟩
  have member : event ∈ Stack b := only.symm ▸ List.mem_cons_self
  have empty (i : Fin A.length) : Stack (bank (A.child i)) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro e on_child
    let c := A.child i
    have inside : (Fcut).parents.Ancestor SourceOf[e] c.val :=
      ((D).mem_contourSavedGapStack Selection S.contour c.val e).mp on_child
    have higher : (Fcut).parents.Ancestor SourceOf[e] parent.val :=
      inside.trans (Fcut).parents ((A.child_parent i) ▸ (Fcut).parents.ancestor_parent c.val)
    have on_parent : e ∈ Stack b := ((D).mem_contourSavedGapStack Selection S.contour parent.val e).mpr higher
    have equal : e = event := List.mem_singleton.mp (only ▸ on_parent)
    subst e
    exact (Fcut).parents.not_ancestor_parent_self c.property ((A.child_parent i).symm ▸ inside)
  have first_name := MetricGluing.bankStack_first_gap_addresses (Parameter := Param)
    Stack b 0 event [] only
  have last_name := MetricGluing.bankStack_last_gap_addresses (Parameter := Param)
    Stack b 0 event [] only
  have tip_ends (flag : Bool) (s : Time) :
      EndAt flag s.1 s.2 = tip ↔
        (flag = true ∧ s = closing) ∨ (flag = false ∧ s = opening) :=
    L.contourGraftTip_endpoint_iff S event g member closing opening
      first_name.2 last_name.1 flag s
  have first_germ : Germ parent true false = (D).boundaryMate Retain (S.contour.cycle.point (A.visit 0)) := by
    have named := ((D).contourParent_firstVisit_germ Selection S.contour (Fcut).boundary_roots
      S.starts parent.val parent.property).symm
    exact named.trans (congrArg (fun j => (D).boundaryMate Retain (S.contour.cycle.point j))
      A.at_first.symm)
  have last_germ : Germ parent false false = S.contour.cycle.point (A.visit (Fin.last A.length)) :=
    ((D).contourParent_lastVisit_germ Selection S.contour (Fcut).boundary_roots
      S.starts parent.val parent.property).symm.trans (congrArg S.contour.cycle.point A.at_last.symm)
  obtain ⟨_, corners⟩ := L.contourGraftRoofRun_endpoints S parent A
    (parent, true, false) (parent, false, false) first_germ last_germ
  let prevFlag (i : Fin (A.length + 1)) : Bool := Fin.cases true (fun _ => false) i
  let nextFlag (i : Fin (A.length + 1)) : Bool := Fin.lastCases false (fun _ => true) i
  let previous (i : Fin (A.length + 1)) : Time := Fin.cases opening time i
  let following (i : Fin (A.length + 1)) : Time := Fin.lastCases closing time i
  let p := contourGraftRoofRunIncoming S A (parent, true, false)
  let q := contourGraftRoofRunOutgoing S A (parent, false, false)
  have prev_data (i : Fin (A.length + 1)) : (p i).2.1 = prevFlag i ∧
      SiteTime (p i) = previous i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨rfl, rfl⟩
    · refine ⟨rfl, ?_⟩
      change RoofTime (bank (A.child j)) false (unitInterval.symm 0) = time j
      rw [unitInterval.symm_zero]
      rfl
  have at_last : q (Fin.last A.length) = (parent, false, false) := by
    change Fin.lastCases (motive := fun _ => Edge × Bool × Bool) (parent, false, false)
      (fun j => (A.child j, true, true)) (Fin.last A.length) = _
    exact Fin.lastCases_last
  have at_mid (j : Fin A.length) : q j.castSucc = (A.child j, true, true) := by
    change Fin.lastCases (motive := fun _ => Edge × Bool × Bool) (parent, false, false)
      (fun j => (A.child j, true, true)) j.castSucc = _
    exact Fin.lastCases_castSucc j
  have after_last : following (Fin.last A.length) = closing := by
    change Fin.lastCases (motive := fun _ => Time) closing time (Fin.last A.length) = closing
    exact Fin.lastCases_last
  have after_mid (j : Fin A.length) : following j.castSucc = time j := by
    change Fin.lastCases (motive := fun _ => Time) closing time j.castSucc = time j
    exact Fin.lastCases_castSucc j
  have flag_exit : nextFlag (Fin.last A.length) = false := by
    change Fin.lastCases (motive := fun _ => Bool) false (fun _ => true) (Fin.last A.length) = false
    exact Fin.lastCases_last
  have flag_next (j : Fin A.length) : nextFlag j.castSucc = true := by
    change Fin.lastCases (motive := fun _ => Bool) false (fun _ => true) j.castSucc = true
    exact Fin.lastCases_castSucc j
  have next_data (i : Fin (A.length + 1)) : (q i).2.1 = nextFlag i ∧
      SiteTime (q i) = following i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [at_last, after_last]
      exact ⟨flag_exit.symm, rfl⟩
    · rw [at_mid, after_mid]
      refine ⟨(flag_next j).symm, ?_⟩
      let e := bank (A.child j)
      let f (k : Fin ((Stack e).length + 1)) : Time := ⟨⟨e, k⟩, 1⟩
      have last_empty : Fin.last (Stack e).length = 0 := by
        apply Fin.ext
        change (Stack e).length = 0
        rw [show Stack e = [] from empty j]
        rfl
      change RoofTime e true (unitInterval.symm 0) = time j
      rw [unitInterval.symm_zero]
      exact congrArg f last_empty
  have exact_ends (i : Fin (A.length + 1)) (flag : Bool) (s : Time) :
      EndAt flag s.1 s.2 = roof i ↔
        (flag = prevFlag i ∧ s = previous i) ∨ (flag = nextFlag i ∧ s = following i) := by
    have h := corners i flag s
    change EndAt flag s.1 s.2 = roof i ↔
      (flag = (p i).2.1 ∧ s = SiteTime (p i)) ∨ (flag = (q i).2.1 ∧ s = SiteTime (q i)) at h
    rw [(prev_data i).1, (prev_data i).2, (next_data i).1, (next_data i).2] at h
    exact h
  have roof_incident (i : Fin (A.length + 1)) (flag : Bool) (s : Time)
      (h : EndAt flag s.1 s.2 = roof i) : s = opening ∨ s = closing ∨ ∃ k, s = time k := by
    rcases (exact_ends i flag s).mp h with ⟨_, heq⟩ | ⟨_, heq⟩
    · revert heq
      refine Fin.cases Or.inl (fun j eq => Or.inr (Or.inr ⟨j, eq⟩)) i
    · revert heq
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact fun eq => Or.inr (Or.inl (eq.trans after_last))
      · exact fun eq => Or.inr (Or.inr ⟨j, eq.trans (after_mid j)⟩)
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
  have distinct (i : Fin (A.length + 1)) : tip ≠ roof i := by
    intro eq
    cases congrArg Sigma.fst eq
  let H := MetricGluing.BankStackCyclicClass.ofSingleBendRunWithSides tip roof opening closing time
    false false ((tip_ends false opening).mpr (Or.inr ⟨rfl, rfl⟩))
    ((exact_ends 0 true opening).mpr (Or.inl ⟨rfl, rfl⟩))
    (fun j => (exact_ends j.castSucc true (time j)).mpr
      (Or.inr ⟨(flag_next j).symm, (after_mid j).symm⟩))
    (fun j => (exact_ends j.succ false (time j)).mpr (Or.inl ⟨rfl, rfl⟩))
    ((exact_ends (Fin.last A.length) false closing).mpr
      (Or.inr ⟨flag_exit.symm, after_last.symm⟩))
    ((tip_ends true closing).mpr (Or.inl ⟨rfl, rfl⟩))
    (fun flag s eq => ((tip_ends flag s).mp eq).elim
      (fun h => Or.inr h.2) (fun h => Or.inl h.2)) roof_incident
  exact ⟨H, rfl, fun _ => rfl, rfl, rfl, empty,
    MetricGluing.BankStackCyclicClass.singleCenter_injective tip roof roof_unique distinct⟩

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
