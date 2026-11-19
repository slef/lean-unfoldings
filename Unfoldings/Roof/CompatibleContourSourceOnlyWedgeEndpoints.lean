module

public import Unfoldings.Metric.BankStackEndpointExistence
public import Unfoldings.Roof.CompatibleContourSourceOnlyRoofWedgeMarks
public import Unfoldings.Roof.CompatibleContourFiniteSeamClasses
public import Unfoldings.Metric.BankStackAdjacentGaps

/-! Recover the actual incident stack slots of a final roof wedge between child excursions. -/

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

local instance sourceOnlyWedgeEndpointsIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlyWedgeEndpointsWholeFintype : Fintype W.Index := W.finiteIndex

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

local notation "Edge" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W
local notation "Retain" => PotentialCutForest.retain Fcut

/-- The exact original roof wedge is the left endpoint at the old child’s first
slot and the right endpoint at the new child’s last slot. -/
theorem compatibleContourSourceOnlyRoofWedge_endpoint_iff
    (old_child new_child : Edge) (j : Fin (contour.length + 1))
    (after_old : finRotate (contour.length + 1) ((D).contourParentInterval Selection contour
      (Fcut).boundary_roots starts old_child.val old_child.property).leave = j)
    (before_new : ((D).contourParentInterval Selection contour (Fcut).boundary_roots starts
      new_child.val new_child.property).enter = j)
    (nonroot : (D).contourOriginalVertex Selection contour j ∉ (Fcut).parents.roots)
    (flag : Bool) (s : Time) :
    let w := (D).boundaryEndVertex Retain (contour.cycle.point j)
    let old_bank := FiniteBank[old_child.val,old_child.property]
    let new_bank := FiniteBank[new_child.val,new_child.property]
    let first : Time := ⟨⟨old_bank, 0⟩, 1⟩
    let last : Time := ⟨⟨new_bank, Fin.last (Stack new_bank).length⟩, 1⟩
    EndAt flag s.1 s.2 = ⟨none, Map ((D).vertexPoint Retain w)⟩ ↔
      (flag = false ∧ s = first) ∨ (flag = true ∧ s = last) := by
  let w := (D).boundaryEndVertex Retain (contour.cycle.point j)
  let x := Map ((D).vertexPoint Retain w)
  let old_bank := FiniteBank[old_child.val,old_child.property]
  let new_bank := FiniteBank[new_child.val,new_child.property]
  let first : Time := ⟨⟨old_bank, 0⟩, 1⟩
  let last : Time := ⟨⟨new_bank, Fin.last (Stack new_bank).length⟩, 1⟩
  have first_name : Named false first.1 first.2 = ⟨old_bank, none, false, 1⟩ := by
    simp [first, MetricGluing.bankStackEndpointAddress, MetricGluing.bankStackLeftAddress]
  have last_name : Named true last.1 last.2 = ⟨new_bank, none, true, 1⟩ := by
    simp [last, MetricGluing.bankStackEndpointAddress, MetricGluing.bankStackRightAddress]
  have name (bank : Attachment) (side : Bool) (t : ParamAt bank) :=
    K.compatibleContourSourceOnlyRoofWedge_baseMark_iff compact nonempty R no_boundary level higher
      M positive inner_disk beta acute contour starts W old_child new_child j after_old before_new
      nonroot bank side t
  constructor
  · intro at_center
    have nodup := K.compatibleContourBankStack_nodup compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour
    have point := (MetricGluing.bankStackAddressPoint_endpoint Stack Pieces Base Gap
      flag s.1 s.2).trans at_center
    let addr := Named flag s.1 s.2
    let valid := MetricGluing.bankStackEndpointAddress_valid Stack flag s.1 s.2
    change Mark addr valid = ⟨none, x⟩ at point
    have recover (a : Addr) (h : Valid a) (eq : Mark a h = ⟨none, x⟩) :
        a = ⟨old_bank, none, false, 1⟩ ∨ a = ⟨new_bank, none, true, 1⟩ := by
      obtain ⟨bank, part, side, t⟩ := a
      cases part with
      | some g => cases congrArg Sigma.fst eq
      | none =>
        have value : Base bank side t = x := eq_of_heq (Sigma.mk.inj eq).2
        rcases (name bank side t).mp value with ⟨times, rfl⟩ | ⟨times, rfl⟩
        · exact Or.inl (congrArg (fun z : Σ b : Attachment, ParamAt b =>
            (⟨z.1, none, false, z.2⟩ : Addr)) times)
        · exact Or.inr (congrArg (fun z : Σ b : Attachment, ParamAt b =>
            (⟨z.1, none, true, z.2⟩ : Addr)) times)
    rcases recover addr valid point with first_eq | last_eq
    · have pair : (flag, s) = (false, first) :=
        MetricGluing.bankStackEndpointAddress_injective Stack nodup (first_eq.trans first_name.symm)
      exact Or.inl ⟨congrArg Prod.fst pair, congrArg Prod.snd pair⟩
    · have pair : (flag, s) = (true, last) :=
        MetricGluing.bankStackEndpointAddress_injective Stack nodup (last_eq.trans last_name.symm)
      exact Or.inr ⟨congrArg Prod.fst pair, congrArg Prod.snd pair⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact (MetricGluing.bankStackEndpoint_eq_of_base_address Stack Pieces Base Gap false first
        old_bank false 1 first_name).trans
        (congrArg (Sigma.mk none) ((name old_bank false 1).mpr (Or.inl ⟨rfl, rfl⟩)))
    · exact (MetricGluing.bankStackEndpoint_eq_of_base_address Stack Pieces Base Gap true last
        new_bank true 1 last_name).trans
        (congrArg (Sigma.mk none) ((name new_bank true 1).mpr (Or.inr ⟨rfl, rfl⟩)))

end Unfoldings.ConvexRoof
