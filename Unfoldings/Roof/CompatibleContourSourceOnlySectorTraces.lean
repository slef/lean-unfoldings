module

public import Unfoldings.Cone.MarkedSectorGerm
public import Unfoldings.Roof.CompatibleContourSourceOnlyBendMarks
public import Unfoldings.Roof.CompatibleContourSourceOnlyFiniteSlotRadii
public import Unfoldings.Roof.CompatibleContourSourceOnlyRoofWedgeChart

/-! Literal initial and terminal arclength rays of the original cross-block sectors. -/

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

local instance sourceOnlySectorTracesIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlySectorTracesWholeFintype : Fintype W.Index := W.finiteIndex

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
local notation "LengthAt[" e "]" => TriangleComplex.positiveContourBankLength D Selection contour e
local notation "IndexAt[" v "," h "," e "," member "]" =>
  TriangleComplex.contourGapBankIndex D Selection contour v h e
    (Iff.mpr (TriangleComplex.mem_contourEdgeGapStack D Selection contour v e)
      (Iff.mp (TriangleComplex.mem_contourSavedGapStack D Selection contour v e) member))
local notation "AngleAt[" e "," j "]" => K.compatibleContourSourceBankFanAngle compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts e j

local notation "BankLength[" v "," h "]" => TriangleComplex.boundaryBankLength D
  (TriangleComplex.contourParentBank D Selection contour (PotentialCutForest.boundary_roots Fcut)
    starts v h false)

/-- The actual gap bend, with the appropriate original incoming or outgoing bank
as its initial ray and the other as its terminal ray. -/
theorem compatibleContourSourceOnlyGapBend_markedSectorGerm
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Fcut).parents.roots)
    (parent_nonroot : (Fcut).parents.parent v ∉ (Fcut).parents.roots)
    (e : Event) (here : e ∈ Stack FiniteBank[v,nonroot])
    (above : e ∈ Stack FiniteBank[(Fcut).parents.parent v,parent_nonroot])
    (strict : ∀ k : Fin LengthAt[e], let B := BankAt[e]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ))
    (side : Bool) :
    let parent := (Fcut).parents.parent v
    let center := Gap FiniteBank[parent,parent_nonroot] e above side 0
    let bank (ray : Bool) (t : unitInterval) :=
      if ray then Gap FiniteBank[v,nonroot] e here side (unitInterval.symm t)
      else Gap FiniteBank[parent,parent_nonroot] e above side t
    let speed (ray : Bool) := if ray then BankLength[v,nonroot] else BankLength[parent,parent_nonroot]
    let saved := AngleAt[e,IndexAt[parent,parent_nonroot,e,above]]
    let θ := if side then saved else 2 * Real.pi - saved
    let ray (b : Bool) := if b then side else !side
    Nonempty (MarkedSectorGerm center θ (fun b => bank (ray b)) (fun b => speed (ray b))) := by
  dsimp only
  obtain ⟨positive_angle, r, positive_radius, chart, center, coords⟩ :=
    K.compatibleContourSourceOnlyGap_parent_bend_marked_chart compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts geometry
      v nonroot parent_nonroot e here above strict side
  refine ⟨⟨⟨positive_angle, r, positive_radius, chart, center⟩, ?_, ?_⟩⟩
  · intro b t
    exact K.compatibleContourSourceOnlyGap_parent_bend_distance compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts geometry
      v nonroot parent_nonroot e here above side (if b then side else !side) t
  · intro b t near
    have h := coords (if b then side else !side) t near
    cases side <;> cases b <;>
      simpa only [Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false, ite_true, ite_false,
        polarRay_zero, Complex.real_smul, mul_one] using h

local notation "Bank[" e "," b "]" => TriangleComplex.contourParentBank D Selection contour
  (PotentialCutForest.boundary_roots Fcut) starts (Subtype.val e) (Subtype.property e) b

private theorem roof_bank_length_side (e : Edge) (side : Bool) :
    (D).boundaryBankLength Bank[e,side] = BankLength[e.val,e.property] := by
  let F := (T).pairedFolding
  have equal := (F.contourParentBank_direction Selection contour (Fcut).boundary_roots starts
    e.val e.property side).trans
      (F.contourParentBank_direction Selection contour (Fcut).boundary_roots starts
        e.val e.property false).symm
  exact (F.boundaryBankLength_eq_germDirection_norm Bank[e,side]).trans
    ((congrArg norm equal).trans (F.boundaryBankLength_eq_germDirection_norm Bank[e,false]).symm)

/-- The roof wedge uses the old child return as its initial ray and the new
child entrance as its terminal ray, with both lengths measured from the parent. -/
theorem compatibleContourSourceOnlyRoofWedge_markedSectorGerm
    (old_child new_child : Edge) (j : Fin (contour.length + 1))
    (after_old : finRotate (contour.length + 1) (Interval[old_child.val,old_child.property]).leave = j)
    (before_new : (Interval[new_child.val,new_child.property]).enter = j)
    (nonroot : (D).contourOriginalVertex Selection contour j ∉ (Fcut).parents.roots) :
    let w := (D).boundaryEndVertex Retain (contour.cycle.point j)
    let x := Map ((D).vertexPoint Retain w)
    let edge (b : Bool) := if b then new_child else old_child
    let mark (b : Bool) (t : unitInterval) := Base (.inl (edge b)) b (unitInterval.symm t)
    let length (b : Bool) := BankLength[(edge b).val,(edge b).property]
    Nonempty (MarkedSectorGerm x ((D).totalAngle Retain w) mark length) := by
  let w := (D).boundaryEndVertex Retain (contour.cycle.point j)
  let x := Map ((D).vertexPoint Retain w)
  let edge (b : Bool) := if b then new_child else old_child
  let mark (b : Bool) (t : unitInterval) := Base (.inl (edge b)) b (unitInterval.symm t)
  let length (b : Bool) := BankLength[(edge b).val,(edge b).property]
  have center (b : Bool) : Base (.inl (edge b)) b 1 = x := by
    have spec := K.compatibleContourSourceOnlyRoofWedge_baseMark_iff compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W old_child new_child j
        after_old before_new nonroot (.inl (edge b)) b 1
    cases b
    · exact spec.mpr (Or.inl ⟨rfl, rfl⟩)
    · exact spec.mpr (Or.inr ⟨rfl, rfl⟩)
  have distance (b : Bool) (t : unitInterval) :
      edist (mark b t) x = ENNReal.ofReal (t.val * length b) := by
    have original := K.compatibleContourSourceOnlyFiniteRoofBank_arclength compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W (edge b) b true t
    change edist (Base (.inl (edge b)) b (unitInterval.symm 0)) (mark b t) = _ at original
    rw [unitInterval.symm_zero, center b, edist_comm] at original
    exact original
  obtain ⟨_, r, rpos, chart, first, last⟩ :=
    K.compatibleContourSourceOnlyRoofWedge_sector_chart compact nonempty R no_boundary level higher
      M positive inner_disk beta acute contour starts W old_child new_child j after_old before_new nonroot
  have center_ball : (chart ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos)⟩).val =
      closedAngularSectorOrigin ((D).totalAngle_pos Retain w).le := by
    apply PolygonalPoint.ext
    have near : edist (Base (.inl old_child) false 1) x < ENNReal.ofReal r :=
      (congrArg (edist · x) (center false)).trans_lt
        ((edist_self x).trans_lt (ENNReal.ofReal_pos.mpr rpos))
    have same : (⟨Base (.inl old_child) false 1, near⟩ : Metric.eball x (ENNReal.ofReal r)) =
        ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos)⟩ := Subtype.ext (center false)
    rw [← same]
    exact (first 1 near).trans (by norm_num [closedAngularSectorOrigin])
  refine ⟨⟨⟨(D).totalAngle_pos Retain w, r, rpos, chart, center_ball⟩, distance, ?_⟩⟩
  intro b t near
  cases b
  · have trace := first (unitInterval.symm t) near
    rw [unitInterval.coe_symm_eq, sub_sub_cancel] at trace
    change (chart ⟨Base (.inl old_child) false (unitInterval.symm t), near⟩).val.val =
      (t.val * BankLength[old_child.val,old_child.property]) • polarRay 0
    simpa only [polarRay_zero, Complex.real_smul, mul_one] using trace
  · have trace := last (unitInterval.symm t) near
    have speed := roof_bank_length_side K compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts new_child true
    rw [unitInterval.coe_symm_eq, sub_sub_cancel, speed] at trace
    exact trace

end Unfoldings.ConvexRoof
