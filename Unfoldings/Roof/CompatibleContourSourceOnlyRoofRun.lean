module

public import Unfoldings.Roof.CompatibleContourSourceOnlyWedgeEndpoints
public import Unfoldings.Roof.CompatibleContourFiniteRoofEndpoints
public import Unfoldings.Complex.ContourParentWedgePartition
public import Unfoldings.Metric.BankStackRoofEndpoints

/-! A run of roof wedges retains its exact two incident signed bank marks at each copy. -/

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

local instance sourceOnlyRoofRunIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlyRoofRunWholeFintype : Fintype W.Index := W.finiteIndex

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


local notation "RoofSite" => Edge × Bool × Bool

/-- Along a roof run the left marks are the previous child returns, with the
specified original incoming site at the first wedge. -/
def contourRoofRunIncoming {parent : (D).Vertex Set.univ}
    {first last : Fin (contour.length + 1)}
    (A : (D).ContourParentWedgeRun Selection contour (Fcut).boundary_roots starts
      parent first last) (initial : RoofSite) (i : Fin (A.length + 1)) : RoofSite :=
  Fin.cases initial (fun j => (A.child j, false, true)) i

/-- Along a roof run the right marks are the next child entrances, with the
specified original outgoing site at the last wedge. -/
def contourRoofRunOutgoing {parent : (D).Vertex Set.univ}
    {first last : Fin (contour.length + 1)}
    (A : (D).ContourParentWedgeRun Selection contour (Fcut).boundary_roots starts
      parent first last) (terminal : RoofSite) (i : Fin (A.length + 1)) : RoofSite :=
  Fin.lastCases terminal (fun j => (A.child j, true, true)) i

/-- Original roof sites specify their actual exterior stack endpoint. -/
def contourRoofSiteTime (site : RoofSite) : Time :=
  RoofTime FiniteBank[site.1.val,site.1.property] site.2.1 (finiteSlotParameterize site.2.2 0)

local notation "SiteTime" => K.contourRoofSiteTime compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "AtSite[" a "]" => Germ (Prod.fst a) (Prod.fst (Prod.snd a))
  (Prod.snd (Prod.snd a))

set_option maxHeartbeats 950000 in
-- The two outward germs and both dependent parameters are kept on their original roof copy.
/-- Calibrate and recognize every literal roof incidence along a run with specified end germs. -/
theorem compatibleContourSourceOnlyRoofRun_endpoints
    (parent : Edge) {first last : Fin (contour.length + 1)}
    (A : (D).ContourParentWedgeRun Selection contour (Fcut).boundary_roots starts
      parent.val first last) (initial terminal : RoofSite)
    (first_germ : AtSite[initial] = (D).boundaryMate Retain (contour.cycle.point (A.visit 0)))
    (last_germ : AtSite[terminal] = contour.cycle.point (A.visit (Fin.last A.length))) :
    let p := K.contourRoofRunIncoming compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts A initial
    let q := K.contourRoofRunOutgoing compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts A terminal
    (∀ i, AtSite[p i] = (D).boundaryMate Retain (contour.cycle.point (A.visit i)) ∧
      AtSite[q i] = contour.cycle.point (A.visit i)) ∧
    ∀ i flag (s : Time), EndAt flag s.1 s.2 = RoofPoint[A.visit i] ↔
      (flag = (p i).2.1 ∧ s = SiteTime (p i)) ∨ (flag = (q i).2.1 ∧ s = SiteTime (q i)) := by
  let p := K.contourRoofRunIncoming compact nonempty R no_boundary level higher M positive
    inner_disk beta acute contour starts A initial
  let q := K.contourRoofRunOutgoing compact nonempty R no_boundary level higher M positive
    inner_disk beta acute contour starts A terminal
  have incoming (i : Fin (A.length + 1)) :
      AtSite[p i] = (D).boundaryMate Retain (contour.cycle.point (A.visit i)) := by
    refine Fin.cases first_germ (fun j => ?_) i
    let c := A.child j
    have step := (contour.next_cyclic (D) (Interval[c.val,c.property]).leave).trans
      (congrArg contour.cycle.point (A.returns j))
    exact ((D).boundaryMate_involutive Retain _).symm.trans
      (congrArg ((D).boundaryMate Retain) step)
  have outgoing (i : Fin (A.length + 1)) :
      AtSite[q i] = contour.cycle.point (A.visit i) := by
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
        (contour.cycle.point (Interval[(A.child j).val,(A.child j).property]).enter)) =
        contour.cycle.point (A.visit j.castSucc)
      exact ((D).boundaryTurn_involutive Retain _).trans (congrArg contour.cycle.point (A.enters j))
  refine ⟨fun i => ⟨incoming i, outgoing i⟩, ?_⟩
  intro i flag s
  have nonroot : (D).contourOriginalVertex Selection contour (A.visit i) ∉ (Fcut).parents.roots :=
    (A.at_visit i).1.symm ▸ parent.property
  let x := Map ((D).vertexPoint Retain ((D).boundaryEndVertex Retain (contour.cycle.point (A.visit i))))
  have names (edge : Attachment) (side : Bool) (t : ParamAt edge) :=
    K.compatibleContourSourceOnlyRoofVertex_baseMark_iff_of_germs compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W (p i).1 (q i).1
      (p i).2.1 (q i).2.1 (p i).2.2 (q i).2.2 (A.visit i)
      (incoming i) (outgoing i) nonroot edge side t
  have nodup := K.compatibleContourBankStack_nodup compact nonempty R no_boundary level higher
    M positive inner_disk beta acute contour
  exact MetricGluing.bankStackEndpoint_eq_base_iff_two_marks Pieces Stack Base Gap nodup x
    (.inl (p i).1) (.inl (q i).1) (p i).2.1 (q i).2.1
    (finiteSlotParameterize (p i).2.2 0) (finiteSlotParameterize (q i).2.2 0) names flag s

set_option maxHeartbeats 700000 in
-- The empty child's first and last slots agree as dependent marked times.
/-- Empty intervening stacks give one common slot between each pair of roof wedges. -/
theorem contourRoofRun_site_times_of_empty
    (parent : Edge) {first last : Fin (contour.length + 1)}
    (A : (D).ContourParentWedgeRun Selection contour (Fcut).boundary_roots starts
      parent.val first last) (initial terminal : RoofSite)
    (empty : ∀ j, Stack FiniteBank[(A.child j).val,(A.child j).property] = []) :
    let p := K.contourRoofRunIncoming compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts A initial
    let q := K.contourRoofRunOutgoing compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts A terminal
    let time (j : Fin A.length) : Time := ⟨⟨.inl (A.child j), 0⟩, 1⟩
    ∀ i, SiteTime (p i) = Fin.cases (SiteTime initial) time i ∧
      SiteTime (q i) = Fin.lastCases (SiteTime terminal) time i ∧
      (p i).2.1 = Fin.cases initial.2.1 (fun _ => false) i ∧
      (q i).2.1 = Fin.lastCases terminal.2.1 (fun _ => true) i := by
  let p := K.contourRoofRunIncoming compact nonempty R no_boundary level higher M positive
    inner_disk beta acute contour starts A initial
  let q := K.contourRoofRunOutgoing compact nonempty R no_boundary level higher M positive
    inner_disk beta acute contour starts A terminal
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

end Unfoldings.ConvexRoof
