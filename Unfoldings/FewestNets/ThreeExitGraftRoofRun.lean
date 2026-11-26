module

public import Unfoldings.FewestNets.ThreeExitRoofVertexMarks
public import Unfoldings.FewestNets.ThreeExitGraftStrictFiber
public import Unfoldings.Complex.ContourParentWedgePartition
public import Unfoldings.Metric.BankStackRoofEndpoints

/-! An ordered run of roof sectors keeps both original endpoint marks. -/

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

local instance graftRoofRunIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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

local notation "RoofSite" => Edge × Bool × Bool

/-- Along a roof run the left marks are the previous child returns, with the
specified original incoming site at the first wedge. -/
def contourGraftRoofRunIncoming {parent : (D).Vertex Set.univ}
    {first last : Fin (S.contour.length + 1)}
    (A : (D).ContourParentWedgeRun Selection S.contour (Fcut).boundary_roots S.starts
      parent first last) (initial : RoofSite) (i : Fin (A.length + 1)) : RoofSite :=
  Fin.cases initial (fun j => (A.child j, false, true)) i

/-- Along a roof run the right marks are the next child entrances, with the
specified original outgoing site at the last wedge. -/
def contourGraftRoofRunOutgoing {parent : (D).Vertex Set.univ}
    {first last : Fin (S.contour.length + 1)}
    (A : (D).ContourParentWedgeRun Selection S.contour (Fcut).boundary_roots S.starts
      parent first last) (terminal : RoofSite) (i : Fin (A.length + 1)) : RoofSite :=
  Fin.lastCases terminal (fun j => (A.child j, true, true)) i

/-- Original roof sites specify their actual exterior stack endpoint. -/
def contourGraftRoofSiteTime (site : RoofSite) : Time :=
  RoofTime FiniteBank[site.1.val,site.1.property] site.2.1 (finiteSlotParameterize site.2.2 0)

local notation "SiteTime" => contourGraftRoofSiteTime S
local notation "AtSite[" a "]" => Germ (Prod.fst a) (Prod.fst (Prod.snd a))
  (Prod.snd (Prod.snd a))

set_option maxHeartbeats 950000 in
-- The two outward germs and both dependent parameters are kept on their original roof copy.
/-- Calibrate and recognize every literal roof incidence along a run with specified end germs. -/
theorem contourGraftRoofRun_endpoints
    (parent : Edge) {first last : Fin (S.contour.length + 1)}
    (A : (D).ContourParentWedgeRun Selection S.contour (Fcut).boundary_roots S.starts
      parent.val first last) (initial terminal : RoofSite)
    (first_germ : AtSite[initial] = (D).boundaryMate Retain (S.contour.cycle.point (A.visit 0)))
    (last_germ : AtSite[terminal] = S.contour.cycle.point (A.visit (Fin.last A.length))) :
    let p := contourGraftRoofRunIncoming S A initial
    let q := contourGraftRoofRunOutgoing S A terminal
    (∀ i, AtSite[p i] = (D).boundaryMate Retain (S.contour.cycle.point (A.visit i)) ∧
      AtSite[q i] = S.contour.cycle.point (A.visit i)) ∧
    ∀ i flag (s : Time), EndAt flag s.1 s.2 = RoofPoint[A.visit i] ↔
      (flag = (p i).2.1 ∧ s = SiteTime (p i)) ∨ (flag = (q i).2.1 ∧ s = SiteTime (q i)) := by
  let p := contourGraftRoofRunIncoming S A initial
  let q := contourGraftRoofRunOutgoing S A terminal
  have incoming (i : Fin (A.length + 1)) :
      AtSite[p i] = (D).boundaryMate Retain (S.contour.cycle.point (A.visit i)) := by
    refine Fin.cases first_germ (fun j => ?_) i
    let c := A.child j
    have step := (S.contour.next_cyclic (D) (Interval[c.val,c.property]).leave).trans
      (congrArg S.contour.cycle.point (A.returns j))
    exact ((D).boundaryMate_involutive Retain _).symm.trans
      (congrArg ((D).boundaryMate Retain) step)
  have outgoing (i : Fin (A.length + 1)) :
      AtSite[q i] = S.contour.cycle.point (A.visit i) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have at_last : q (Fin.last A.length) = terminal := by
        change Fin.lastCases (motive := fun _ => RoofSite) terminal
          (fun j => (A.child j, true, true)) (Fin.last A.length) = terminal
        exact Fin.lastCases_last
      rw [at_last]
      exact last_germ
    · have at_child : q j.castSucc = (A.child j, true, true) := by
        change Fin.lastCases (motive := fun _ => RoofSite) terminal
          (fun j => (A.child j, true, true)) j.castSucc = _
        exact Fin.lastCases_castSucc j
      rw [at_child]
      change (D).boundaryTurn Retain ((D).boundaryTurn Retain
        (S.contour.cycle.point (Interval[(A.child j).val,(A.child j).property]).enter)) =
        S.contour.cycle.point (A.visit j.castSucc)
      exact ((D).boundaryTurn_involutive Retain _).trans (congrArg S.contour.cycle.point (A.enters j))
  refine ⟨fun i => ⟨incoming i, outgoing i⟩, ?_⟩
  intro i flag s
  have nonroot : (D).contourOriginalVertex Selection S.contour (A.visit i) ∉ (Fcut).parents.roots :=
    (A.at_visit i).1.symm ▸ parent.property
  let x := Map ((D).vertexPoint Retain ((D).boundaryEndVertex Retain (S.contour.cycle.point (A.visit i))))
  have names (edge : Attachment) (side : Bool) (t : Param edge) :=
    L.contourRoofVertex_baseMark_iff_of_germs S (p i).1 (q i).1
      (p i).2.1 (q i).2.1 (p i).2.2 (q i).2.2 (A.visit i)
      (incoming i) (outgoing i) nonroot edge side t
  have nodup := contourGraft_stack_nodup S
  exact MetricGluing.bankStackEndpoint_eq_base_iff_two_marks Pieces Stack Base Gap nodup x
    (.inl (p i).1) (.inl (q i).1) (p i).2.1 (q i).2.1
    (finiteSlotParameterize (p i).2.2 0) (finiteSlotParameterize (q i).2.2 0) names flag s

set_option maxHeartbeats 700000 in
-- The empty child's first and last slots agree as dependent marked times.
/-- Empty intervening stacks give one common slot between each pair of roof wedges. -/
theorem contourGraftRoofRun_site_times_of_empty
    (parent : Edge) {first last : Fin (S.contour.length + 1)}
    (A : (D).ContourParentWedgeRun Selection S.contour (Fcut).boundary_roots S.starts
      parent.val first last) (initial terminal : RoofSite)
    (empty : ∀ j, Stack FiniteBank[(A.child j).val,(A.child j).property] = []) :
    let p := contourGraftRoofRunIncoming S A initial
    let q := contourGraftRoofRunOutgoing S A terminal
    let time (j : Fin A.length) : Time := ⟨⟨.inl (A.child j), 0⟩, 1⟩
    ∀ i, SiteTime (p i) = Fin.cases (SiteTime initial) time i ∧
      SiteTime (q i) = Fin.lastCases (SiteTime terminal) time i ∧
      (p i).2.1 = Fin.cases initial.2.1 (fun _ => false) i ∧
      (q i).2.1 = Fin.lastCases terminal.2.1 (fun _ => true) i := by
  let p := contourGraftRoofRunIncoming S A initial
  let q := contourGraftRoofRunOutgoing S A terminal
  let time (j : Fin A.length) : Time := ⟨⟨.inl (A.child j), 0⟩, 1⟩
  have first (i : Fin (A.length + 1)) : SiteTime (p i) = Fin.cases (SiteTime initial) time i ∧
      (p i).2.1 = Fin.cases initial.2.1 (fun _ => false) i := by
    refine Fin.cases ⟨rfl, rfl⟩ (fun j => ⟨?_, rfl⟩) i
    change RoofTime FiniteBank[(A.child j).val,(A.child j).property] false
      (unitInterval.symm 0) = time j
    rw [unitInterval.symm_zero]
    rfl
  have last (i : Fin (A.length + 1)) :
      SiteTime (q i) = Fin.lastCases (SiteTime terminal) time i ∧
      (q i).2.1 = Fin.lastCases terminal.2.1 (fun _ => true) i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have label : q (Fin.last A.length) = terminal := by
        change Fin.lastCases (motive := fun _ => RoofSite) terminal
          (fun j => (A.child j, true, true)) (Fin.last A.length) = terminal
        exact Fin.lastCases_last
      rw [label, Fin.lastCases_last, Fin.lastCases_last]
      exact ⟨rfl, rfl⟩
    · have label : q j.castSucc = (A.child j, true, true) := by
        change Fin.lastCases (motive := fun _ => RoofSite) terminal
          (fun j => (A.child j, true, true)) j.castSucc = _
        exact Fin.lastCases_castSucc j
      rw [label, Fin.lastCases_castSucc, Fin.lastCases_castSucc]
      refine ⟨?_, rfl⟩
      let b := FiniteBank[(A.child j).val,(A.child j).property]
      let at_slot (k : Fin ((Stack b).length + 1)) : Time := ⟨⟨b, k⟩, 1⟩
      have same : Fin.last (Stack b).length = 0 := by
        apply Fin.ext
        change (Stack b).length = 0
        rw [show Stack b = [] from empty j]
        rfl
      change RoofTime b true (unitInterval.symm 0) = time j
      rw [unitInterval.symm_zero]
      exact congrArg at_slot same
  exact fun i => ⟨(first i).1, (last i).1, (first i).2, (last i).2⟩

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
