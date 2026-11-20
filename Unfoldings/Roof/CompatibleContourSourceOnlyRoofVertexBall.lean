module

public import Unfoldings.Roof.CompatibleContourSourceOnlyIncomingVertexBall
public import Unfoldings.Roof.CompatibleContourSourceOnlyRoofRun

/-! Every original roof wedge at a nonroot vertex lies in a planar ball. -/

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

local instance sourceOnlyRoofVertexBallIndexFintype : Fintype (T).Index :=
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
  (geometry : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    OrientedBankGap
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance sourceOnlyRoofVertexBallWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "models" => (fun event : Event => OrientedBankGap.model (geometry event))
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

local notation "Point" => MetricGluing.point Pieces Banks
local notation "LengthAt[" e "]" => TriangleComplex.positiveContourBankLength D Selection contour e
local notation "Terminal" => TriangleComplex.ContourTerminalEdge D Selection

local notation "Germ" => K.compatibleContourFiniteRoofGerm compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts
local notation "Visit[" j "]" => TriangleComplex.contourOriginalVertex D Selection contour j
local notation "SiteTime" => K.contourRoofSiteTime compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour

set_option maxHeartbeats 2400000 in
-- The original roof wedge carries two dependent addresses, one on each adjacent child excursion.
/-- Every original roof copy at a nonroot vertex reaches a named outgoing slot.
Empty children restore their seams and nonempty children reach it through a gap. -/
theorem compatibleContourSourceOnlyRoofVertex_eq_outgoing
    (j : Fin (contour.length + 1)) (nonroot : Visit[j] ∉ (Fcut).parents.roots) :
    let b := FiniteBank[Visit[j],nonroot]
    ∃ k : Fin ((Stack b).length + 1), Point RoofPoint[j] = Point (EndAt true ⟨b, k⟩ 0) := by
  let parent : Edge := ⟨Visit[j], nonroot⟩
  let A := (D).contourFullParentWedgeRun Selection contour (Fcut).boundary_roots starts parent
  let b := FiniteBank[parent.val,parent.property]
  let data := Interval[parent.val,parent.property]
  have bounds := (data.subtree j).mp ((Fcut).parents.ancestor_refl parent.val)
  have offset := (D).contourParentInterval_enter_succ_val Selection contour (Fcut).boundary_roots
    starts parent.val parent.property
  have above_first : finRotate (contour.length + 1) data.enter ≤ j := by
    change (finRotate (contour.length + 1) data.enter).val ≤ j.val
    change data.enter.val < j.val ∧ j.val ≤ data.leave.val at bounds
    change (finRotate (contour.length + 1) data.enter).val = data.enter.val + 1 at offset
    omega
  obtain ⟨v, at_j⟩ := (A.visits j).mpr ⟨rfl, above_first, bounds.2⟩
  have first_germ : Germ parent true false =
      (D).boundaryMate Retain (contour.cycle.point (A.visit 0)) :=
    ((D).contourParent_firstVisit_germ Selection contour (Fcut).boundary_roots starts
      parent.val parent.property).symm.trans
      (congrArg (fun i => (D).boundaryMate Retain (contour.cycle.point i)) A.at_first.symm)
  have last_germ : Germ parent false false = contour.cycle.point (A.visit (Fin.last A.length)) :=
    ((D).contourParent_lastVisit_germ Selection contour (Fcut).boundary_roots starts
      parent.val parent.property).symm.trans (congrArg contour.cycle.point A.at_last.symm)
  obtain ⟨_, endpoints⟩ := K.compatibleContourSourceOnlyRoofRun_endpoints compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W models parent A
    (parent, true, false) (parent, false, false) first_germ last_germ
  let outgoing (z : MetricGluing.Realization Pieces Banks) : Prop :=
    ∃ k : Fin ((Stack b).length + 1), z = Point (EndAt true ⟨b, k⟩ 0)
  have every (i : Fin (A.length + 1)) : outgoing (Point RoofPoint[A.visit i]) := by
    induction i using Fin.inductionOn with
    | zero =>
      let s : Time := ⟨⟨b, Fin.last (Stack b).length⟩, 0⟩
      have label : EndAt true s.1 s.2 = RoofPoint[A.visit 0] :=
        (endpoints 0 true s).mpr (Or.inl ⟨rfl, rfl⟩)
      exact ⟨Fin.last (Stack b).length, congrArg Point label.symm⟩
    | succ i ih =>
      let child := A.child i
      let a := FiniteBank[child.val,child.property]
      let s : Time := ⟨⟨a, 0⟩, 1⟩
      have label : L s.1 s.2 = RoofPoint[A.visit i.succ] := by
        apply (endpoints i.succ false s).mpr
        refine Or.inl ⟨rfl, ?_⟩
        change s = ⟨⟨a, 0⟩, unitInterval.symm 0⟩
        rw [unitInterval.symm_zero]
      have held : outgoing (Point (L s.1 s.2)) := by
        by_cases empty : Stack a = []
        · have same_slot : Fin.last (Stack a).length = 0 := by
            apply Fin.ext
            change (Stack a).length = 0
            rw [empty]
            rfl
          let q := K.contourRoofRunOutgoing compact nonempty R no_boundary level higher M positive
            inner_disk beta acute contour starts A (parent, false, false)
          have prior_site : q i.castSucc = (child, true, true) := by
            change Fin.lastCases (motive := fun _ => Edge × Bool × Bool)
              (parent, false, false) (fun j => (A.child j, true, true)) i.castSucc = _
            exact Fin.lastCases_castSucc i
          have prev_label : Rgt s.1 s.2 = RoofPoint[A.visit i.castSucc] := by
            apply (endpoints i.castSucc true s).mpr
            right
            change true = (q i.castSucc).2.1 ∧ s = SiteTime (q i.castSucc)
            rw [prior_site]
            refine ⟨rfl, ?_⟩
            change s = ⟨⟨a, Fin.last (Stack a).length⟩, unitInterval.symm 0⟩
            rw [same_slot, unitInterval.symm_zero]
          have glued : Point (L s.1 s.2) = Point (Rgt s.1 s.2) :=
            MetricGluing.point_eq_of_glue Pieces (glue := Banks) ⟨s.1, s.2, rfl, rfl⟩
          obtain ⟨k, h⟩ := ih
          exact ⟨k, glued.trans ((congrArg Point prev_label).trans h)⟩
        · have hp : (Fcut).parents.parent child.val ∉ (Fcut).parents.roots :=
            (A.child_parent i).symm ▸ nonroot
          obtain ⟨k, witness⟩ := K.compatibleContourSourceOnlyFiniteEnd_nonempty_eq_outgoing
            compact nonempty R no_boundary level higher M positive inner_disk beta acute contour
            starts W geometry child hp empty 0
          let atParent (p : Edge) : Prop :=
            let a := FiniteBank[p.val,p.property]
            ∃ k : Fin ((Stack a).length + 1), Point (L s.1 s.2) = Point (EndAt true ⟨a, k⟩ 0)
          have with_child : atParent ⟨(Fcut).parents.parent child.val, hp⟩ := ⟨k, witness⟩
          have same : (⟨(Fcut).parents.parent child.val, hp⟩ : Edge) = parent :=
            Subtype.ext (A.child_parent i)
          exact Eq.mp (congrArg atParent same) with_child
      obtain ⟨k, h⟩ := held
      exact ⟨k, (congrArg Point label).symm.trans h⟩
  exact Eq.mp (congrArg (fun i => outgoing (Point RoofPoint[i])) at_j) (every v)

/-- The entire contour run at a nonroot vertex is planar after grafting. Empty
children transport the chart across their restored seams, and nonempty children
supply it from their adjoining gaps. -/
theorem compatibleContourSourceOnlyRoofVertex_planarBall
    (ends : Visit[Fin.last contour.length] ∈ (Fcut).parents.roots)
    (strict : ∀ (e : Event) (k : Fin LengthAt[e]), let B := BankAt[e]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ))
    (j : Fin (contour.length + 1)) (nonroot : Visit[j] ∉ (Fcut).parents.roots) :
    HasMetricBallChart ℂ (Point RoofPoint[j]) := by
  obtain ⟨k, named⟩ := K.compatibleContourSourceOnlyRoofVertex_eq_outgoing compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W geometry j nonroot
  have chart := K.compatibleContourSourceOnly_outgoingVertex_planarBall compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W geometry ends
    ⟨Visit[j], nonroot⟩ strict k
  exact Eq.mpr (congrArg (HasMetricBallChart ℂ) named) chart

set_option maxHeartbeats 1750000 in
/-- The restored end of an empty child stack lies at an outgoing slot of its parent. -/
theorem compatibleContourSourceOnlyFiniteEnd_empty_eq_outgoing
    (child : Edge) (hp : (Fcut).parents.parent child.val ∉ (Fcut).parents.roots)
    (empty : Stack FiniteBank[child.val,child.property] = [])
    (i : Fin ((Stack FiniteBank[child.val,child.property]).length + 1)) :
    let b := FiniteBank[(Fcut).parents.parent child.val,hp]
    ∃ k : Fin ((Stack b).length + 1),
      Point (L ⟨FiniteBank[child.val,child.property], i⟩ 1) = Point (EndAt true ⟨b, k⟩ 0) := by
  let a := FiniteBank[child.val,child.property]
  let data := Interval[child.val,child.property]
  have at_parent : Visit[data.enter] = (Fcut).parents.parent child.val :=
    ((D).contourParentInterval_entry_original Selection contour (Fcut).boundary_roots starts
      child.val child.property).1
  have i0 : i = 0 := by
    apply Fin.ext
    have bound : i.val < (Stack a).length + 1 := i.isLt
    have len : (Stack a).length = 0 := congrArg List.length empty
    change i.val = 0
    omega
  have roof_mark : Base a true 1 = (RoofPoint[data.enter]).2 := by
    have mark := K.compatibleContourFiniteRoofGerm_mark compact nonempty R no_boundary level higher
      M positive inner_disk beta acute contour starts W child true true 0
    have turn : Germ child true true = contour.cycle.point data.enter :=
      (D).boundaryTurn_involutive Retain _
    change Base a true (unitInterval.symm 0) =
      Map ((D).directedBoundaryPath (Germ child true true) 0) at mark
    rw [unitInterval.symm_zero, turn] at mark
    exact mark.trans (congrArg Map ((D).directedBoundaryPath_zero (contour.cycle.point data.enter)))
  have mark := MetricGluing.bankStackEndpoint_eq_of_base_address Stack Pieces Base Gap true
    (⟨⟨a, 0⟩, 1⟩ : Time) a true 1
    (MetricGluing.bankStack_empty_addresses (Parameter := ParamAt) Stack a 1 empty).2
  have same : Point (L ⟨a, 0⟩ 1) = Point RoofPoint[data.enter] := by
    have glue : Point (L ⟨a, 0⟩ 1) = Point (Rgt ⟨a, 0⟩ 1) :=
      MetricGluing.point_eq_of_glue Pieces (glue := Banks) ⟨⟨a, 0⟩, 1, rfl, rfl⟩
    exact glue.trans (congrArg Point (mark.trans (congrArg (Sigma.mk none) roof_mark)))
  obtain ⟨k, hk⟩ := K.compatibleContourSourceOnlyRoofVertex_eq_outgoing compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W geometry data.enter
    (at_parent.symm ▸ hp)
  let P (v : Edge) := ∃ k : Fin ((Stack (.inl v)).length + 1),
    Point (L ⟨a, i⟩ 1) = Point (EndAt true ⟨.inl v, k⟩ 0)
  have at_visit : P ⟨Visit[data.enter], at_parent.symm ▸ hp⟩ := by
    refine ⟨k, ?_⟩
    rw [i0]
    exact same.trans hk
  exact Eq.mp (congrArg P (Subtype.ext at_parent)) at_visit

set_option maxHeartbeats 1500000 in
-- The reversed child entrance retains its original tagged roof copy.
/-- An empty stack at the upper end of a nonterminal child is glued at an
original roof wedge of its parent. -/
theorem compatibleContourSourceOnlyFiniteEnd_empty_planarBall
    (ends : Visit[Fin.last contour.length] ∈ (Fcut).parents.roots)
    (strict : ∀ (e : Event) (k : Fin LengthAt[e]), let B := BankAt[e]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ))
    (child : Edge) (hp : (Fcut).parents.parent child.val ∉ (Fcut).parents.roots)
    (empty : Stack FiniteBank[child.val,child.property] = [])
    (i : Fin ((Stack FiniteBank[child.val,child.property]).length + 1)) :
    HasMetricBallChart ℂ (Point (L ⟨FiniteBank[child.val,child.property], i⟩ 1)) := by
  obtain ⟨k, hk⟩ := K.compatibleContourSourceOnlyFiniteEnd_empty_eq_outgoing compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W geometry child hp empty i
  exact Eq.mpr (congrArg (HasMetricBallChart ℂ) hk)
    (K.compatibleContourSourceOnly_outgoingVertex_planarBall compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W geometry ends
      ⟨(Fcut).parents.parent child.val, hp⟩ strict k)

end Unfoldings.ConvexRoof
