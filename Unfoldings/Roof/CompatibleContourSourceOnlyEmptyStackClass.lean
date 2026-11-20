module

public import Unfoldings.Roof.CompatibleContourSourceOnlyRoofRun
public import Unfoldings.Metric.BankStackRoofCycle

/-! The empty outgoing stack restores every original wedge of its parent. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)
  (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
  (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ slopes)
  (beta : 0 ≤ β) (acute : β < Real.pi / 2)

local notation "T" => K.compatibleCutMesh compact nonempty R no_boundary level higher M
  positive inner_disk
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance sourceOnlyEmptyStackIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
variable (contour :
    (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.BoundaryContour
    ((K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.selectedRetain
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection))
  (starts : (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.contourOriginalVertex
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour 0 ∈
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).parents.roots)
  (W : R.WholeCutModel M)
  (models : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    BankGapModel
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance sourceOnlyEmptyStackWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Pieces" => polygonalBankStackPiece W.Cut
  (fun event : Event => BankGapModel.region (models event))
local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "Gap" => K.compatibleContourSourceOnlyGapMark compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts models

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "FiniteBank[" v "," h "]" => (Sum.inl (Subtype.mk v h) : Attachment)
local notation "Addr" => MetricGluing.BankStackAddress (G := Event) (Parameter := ParamAt)
local notation "Named" => MetricGluing.bankStackEndpointAddress (Parameter := ParamAt) Stack
local notation "Mark" => MetricGluing.bankStackAddressPoint Stack Pieces Base Gap
local notation "Valid" => MetricGluing.BankStackAddressValid Stack
local notation "EndAt" => MetricGluing.bankStackEndpoint Stack Pieces Base Gap
local notation "L" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Rgt" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams L Rgt
local notation "Time" => (Σ s : MetricGluing.BankStackSlot Stack, ParamAt (Sigma.fst s))

local notation "BankAt[" e "]" => K.compatibleContourSourceBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "MovedAt[" e "]" => K.compatibleContourSourceOnlyBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e


local notation "Edge" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Interval[" v "," h "]" => TriangleComplex.contourParentInterval
  D Selection contour (PotentialCutForest.boundary_roots Fcut) starts v h
local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W
local notation "Retain" => PotentialCutForest.retain Fcut
local notation "SourceOf[" e "]" => TriangleComplex.positiveContourVertex D Selection contour e
local notation "RoofPoint[" j "]" => (Sigma.mk none (Map
  (TriangleComplex.vertexPoint D Retain (TriangleComplex.boundaryEndVertex D Retain
    (PairedInvolutions.System.Chain.point (TriangleComplex.BoundaryContour.cycle contour) j)))) :
      MetricGluing.Total Pieces)



local notation "Germ" => K.compatibleContourFiniteRoofGerm compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts
local notation "RoofTime" => MetricGluing.bankStackRoofTime (Parameter := ParamAt) Stack



local notation "SiteTime" => K.contourRoofSiteTime compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour

set_option maxHeartbeats 1700000 in
-- The closing slot and all the original wedge times are dependent on their stack lengths.
/-- An empty outgoing stack gives the exact restored cycle of the original roof copies. -/
theorem exists_compatibleContourSourceOnlyEmptyStackClass (parent : Edge)
    (none_added : Stack FiniteBank[parent.val,parent.property] = []) :
    let A := (D).contourFullParentWedgeRun Selection contour (Fcut).boundary_roots starts parent
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
  let A := (D).contourFullParentWedgeRun Selection contour (Fcut).boundary_roots starts parent
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
      ((D).mem_contourSavedGapStack Selection contour c.val e).mp on_child
    have higher : (Fcut).parents.Ancestor SourceOf[e] parent.val :=
      inside.trans (Fcut).parents ((A.child_parent i) ▸ (Fcut).parents.ancestor_parent c.val)
    have on_parent : e ∈ Stack b :=
      ((D).mem_contourSavedGapStack Selection contour parent.val e).mpr higher
    exact List.not_mem_nil (none_added ▸ on_parent)
  have wrap : Fin.last (Stack b).length = 0 := by
    apply Fin.ext
    change (Stack b).length = 0
    rw [none_added]
    rfl
  have first_time : SiteTime (parent, true, false) = closing :=
    congrArg (fun i : Fin ((Stack b).length + 1) => (⟨⟨b, i⟩, 0⟩ : Time)) wrap
  have last_time : SiteTime (parent, false, false) = closing := rfl
  have first_germ : Germ parent true false = (D).boundaryMate Retain (contour.cycle.point (A.visit 0)) :=
    ((D).contourParent_firstVisit_germ Selection contour (Fcut).boundary_roots starts
      parent.val parent.property).symm.trans
      (congrArg (fun j => (D).boundaryMate Retain (contour.cycle.point j)) A.at_first.symm)
  have last_germ : Germ parent false false = contour.cycle.point (A.visit (Fin.last A.length)) :=
    ((D).contourParent_lastVisit_germ Selection contour (Fcut).boundary_roots starts
      parent.val parent.property).symm.trans (congrArg contour.cycle.point A.at_last.symm)
  obtain ⟨_, corners⟩ := K.compatibleContourSourceOnlyRoofRun_endpoints compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W models parent A
    (parent, true, false) (parent, false, false) first_germ last_germ
  have site_times := K.contourRoofRun_site_times_of_empty compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts parent A (parent, true, false)
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
      (contour.cycle.point (A.visit k))
    have value : Map ((D).vertexPoint Retain (copy i)) = Map ((D).vertexPoint Retain (copy j)) :=
      eq_of_heq (Sigma.mk.inj same).2
    have nonroot : (D).contourOriginalVertex Selection contour (A.visit i) ∉ (Fcut).parents.roots :=
      (A.at_visit i).1.symm ▸ parent.property
    have below := K.compatibleContourRoofVertex_height_lt_of_nonroot compact nonempty R no_boundary
      level higher M positive inner_disk beta acute (copy i) nonroot
    have equal := K.compatibleMeshWholeMap_injective_at compact nonempty R no_boundary level higher
      M positive inner_disk beta acute W ((D).vertexPoint Retain (copy i)) below
      ((D).vertexPoint Retain (copy j)) value
    exact A.visit.injective ((D).boundaryCycle_vertices_injective Retain contour.cycle contour.closes
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

end Unfoldings.ConvexRoof
