module

public import Unfoldings.FewestNets.ThreeExitGraftRoofRun
public import Unfoldings.Metric.BankStackRoofCycle


/-! Cyclic roof incidences at a vertex with an empty outgoing stack. -/

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

local instance graftEmptyStackClassIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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
local notation "RoofSite" => Edge × Bool × Bool
local notation "SiteTime" => contourGraftRoofSiteTime S
local notation "AtSite[" a "]" => Germ (Prod.fst a) (Prod.fst (Prod.snd a))
  (Prod.snd (Prod.snd a))

set_option maxHeartbeats 1700000 in
-- The closing slot and all the original wedge times are dependent on their stack lengths.
/-- An empty outgoing stack gives the exact restored cycle of the original roof copies. -/
theorem exists_contourGraftEmptyStackClass (parent : Edge)
    (none_added : Stack FiniteBank[parent.val,parent.property] = []) :
    let A := (D).contourFullParentWedgeRun Selection S.contour (Fcut).boundary_roots S.starts parent
    let b := FiniteBank[parent.val,parent.property]
    let closing : Time := ⟨⟨b, 0⟩, 0⟩
    ∃ H : MetricGluing.BankStackCyclicClass Pieces Stack Base Gap A.length,
      H.center 0 = EndAt true closing.1 closing.2 ∧
      (∀ i, H.center i = RoofPoint[A.visit i]) ∧
      H.time = MetricGluing.BankStackCyclicClass.roofTime closing
        (fun i => ⟨⟨FiniteBank[(A.child i).val,(A.child i).property], 0⟩, 1⟩) ∧
      H.side = MetricGluing.BankStackCyclicClass.roofSide ∧
      (∀ i, Stack FiniteBank[(A.child i).val,(A.child i).property] = []) ∧
      Function.Injective H.center := by
  let A := (D).contourFullParentWedgeRun Selection S.contour (Fcut).boundary_roots S.starts parent
  let b := FiniteBank[parent.val,parent.property]
  let closing : Time := ⟨⟨b, 0⟩, 0⟩
  let roof (i : Fin (A.length + 1)) := RoofPoint[A.visit i]
  let bank (e : Edge) := FiniteBank[e.val,e.property]
  let time (i : Fin A.length) : Time := ⟨⟨bank (A.child i), 0⟩, 1⟩
  have empty (i : Fin A.length) : Stack (bank (A.child i)) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro e on_child
    let c := A.child i
    have inside : (Fcut).parents.Ancestor SourceOf[e] c.val :=
      ((D).mem_contourSavedGapStack Selection S.contour c.val e).mp on_child
    have higher : (Fcut).parents.Ancestor SourceOf[e] parent.val :=
      inside.trans (Fcut).parents ((A.child_parent i) ▸ (Fcut).parents.ancestor_parent c.val)
    have on_parent : e ∈ Stack b :=
      ((D).mem_contourSavedGapStack Selection S.contour parent.val e).mpr higher
    exact List.not_mem_nil (none_added ▸ on_parent)
  have wrap : Fin.last (Stack b).length = 0 := by
    apply Fin.ext
    change (Stack b).length = 0
    rw [none_added]
    rfl
  have first_time : SiteTime (parent, true, false) = closing :=
    congrArg (fun i : Fin ((Stack b).length + 1) => (⟨⟨b, i⟩, 0⟩ : Time)) wrap
  have last_time : SiteTime (parent, false, false) = closing := rfl
  have first_germ : Germ parent true false = (D).boundaryMate Retain (S.contour.cycle.point (A.visit 0)) :=
    ((D).contourParent_firstVisit_germ Selection S.contour (Fcut).boundary_roots S.starts
      parent.val parent.property).symm.trans
      (congrArg (fun j => (D).boundaryMate Retain (S.contour.cycle.point j)) A.at_first.symm)
  have last_germ : Germ parent false false = S.contour.cycle.point (A.visit (Fin.last A.length)) :=
    ((D).contourParent_lastVisit_germ Selection S.contour (Fcut).boundary_roots S.starts
      parent.val parent.property).symm.trans (congrArg S.contour.cycle.point A.at_last.symm)
  obtain ⟨_, corners⟩ := L.contourGraftRoofRun_endpoints S parent A
    (parent, true, false) (parent, false, false) first_germ last_germ
  have site_times := contourGraftRoofRun_site_times_of_empty S parent A (parent, true, false)
    (parent, false, false) empty
  let prevFlag (i : Fin (A.length + 1)) : Bool := Fin.cases true (fun _ => false) i
  let nextFlag (i : Fin (A.length + 1)) : Bool := MetricGluing.BankStackCyclicClass.roofSide i
  let prevTime (i : Fin (A.length + 1)) : Time := Fin.cases closing time i
  let nextTime (i : Fin (A.length + 1)) : Time :=
    MetricGluing.BankStackCyclicClass.roofTime closing time i
  have exact_ends (i : Fin (A.length + 1)) (flag : Bool) (s : Time) :
      EndAt flag s.1 s.2 = roof i ↔
        (flag = prevFlag i ∧ s = prevTime i) ∨ (flag = nextFlag i ∧ s = nextTime i) := by
    have h := corners i flag s
    have data := site_times i
    rw [data.1, data.2.1, data.2.2.1, data.2.2.2, first_time, last_time] at h
    exact h

  have incident (i : Fin (A.length + 1)) (flag : Bool) (s : Time)
      (h : EndAt flag s.1 s.2 = roof i) : s = closing ∨ ∃ k, s = time k := by
    rcases (exact_ends i flag s).mp h with ⟨_, t⟩ | ⟨_, t⟩
    · revert t
      exact Fin.cases Or.inl (fun j h => Or.inr ⟨j, h⟩) i
    · revert t
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact fun h => Or.inl (h.trans (MetricGluing.BankStackCyclicClass.roofTime_last closing time))
      · exact fun h => Or.inr ⟨j, h.trans
          (MetricGluing.BankStackCyclicClass.roofTime_between closing time j)⟩
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
  have final_mark : EndAt false closing.1 closing.2 = roof (Fin.last A.length) :=
    (exact_ends (Fin.last A.length) false closing).mpr (Or.inr
      ⟨MetricGluing.BankStackCyclicClass.roofSide_last.symm,
        (MetricGluing.BankStackCyclicClass.roofTime_last closing time).symm⟩)
  have first_mark : EndAt true closing.1 closing.2 = roof 0 :=
    (exact_ends 0 true closing).mpr (Or.inl ⟨rfl, rfl⟩)
  let H := MetricGluing.BankStackCyclicClass.ofClosedRoofRun roof closing time
    (fun i => (exact_ends i.castSucc true (time i)).mpr (Or.inr
      ⟨(MetricGluing.BankStackCyclicClass.roofSide_between i).symm,
        (MetricGluing.BankStackCyclicClass.roofTime_between closing time i).symm⟩))
    (fun i => (exact_ends i.succ false (time i)).mpr (Or.inl ⟨rfl, rfl⟩))
    final_mark first_mark incident
  exact ⟨H, first_mark.symm, fun _ => rfl, rfl, rfl, empty, roof_unique⟩

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
