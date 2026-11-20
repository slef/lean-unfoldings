module

public import Unfoldings.Metric.BankStackCurveMetric
public import Unfoldings.Metric.BankStackCyclicClass
public import Unfoldings.Roof.CompatibleContourSourceOnlyGraftCells

/-! Exact arclength measured from either endpoint of a finite original seam slot. -/

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

local instance sourceOnlyFiniteSlotRadiiIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlyFiniteSlotRadiiWholeFintype : Fintype W.Index := W.finiteIndex

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
local notation "Time" => (Σ slot : MetricGluing.BankStackSlot Stack, ParamAt (Sigma.fst slot))
local notation "LeftCurve" => MetricGluing.bankStackLeftCurve Stack Pieces Base Gap

local notation "Edge" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "BankLength[" v "," h "]" => TriangleComplex.boundaryBankLength D
  (TriangleComplex.contourParentBank D Selection contour (PotentialCutForest.boundary_roots Fcut)
    starts v h false)

def finiteSlotParameterize (reverse : Bool) : unitInterval ≃ unitInterval :=
  if reverse then unitInterval.symmHomeomorph.toEquiv else Equiv.refl _

omit beta acute in
private theorem edist_finiteSlotParameterize (reverse : Bool) (t : unitInterval) :
    edist (finiteSlotParameterize reverse 0) (finiteSlotParameterize reverse t) =
      ENNReal.ofReal t.val := by
  cases reverse
  · change edist (0 : unitInterval) t = ENNReal.ofReal t.val
    rw [edist_dist]
    apply congrArg ENNReal.ofReal
    change dist (0 : ℝ) t.val = t.val
    rw [dist_comm, Real.dist_eq, sub_zero, abs_of_nonneg t.property.1]
  · change edist (unitInterval.symm 0) (unitInterval.symm t) = ENNReal.ofReal t.val
    rw [edist_dist, unitInterval.symm_zero]
    apply congrArg ENNReal.ofReal
    change dist (1 : ℝ) (unitInterval.symm t).val = t.val
    rw [Real.dist_eq, unitInterval.coe_symm_eq, sub_sub_cancel, abs_of_nonneg t.property.1]

/-- Both original copies of a finite roof bank have the same exact arclength,
measured from the chosen endpoint. -/
theorem compatibleContourSourceOnlyFiniteRoofBank_arclength
    (e : Edge) (side reverse : Bool) (t : unitInterval) :
    let b := FiniteBank[e.val,e.property]
    edist (Base b side (finiteSlotParameterize reverse 0))
      (Base b side (finiteSlotParameterize reverse t)) =
      ENNReal.ofReal (t.val * BankLength[e.val,e.property]) := by
  let bank := FiniteBank[e.val,e.property]
  let u := finiteSlotParameterize reverse (0 : unitInterval)
  let v := finiteSlotParameterize reverse t
  let b := (D).contourParentBank Selection contour (Fcut).boundary_roots starts e.val e.property false
  have both := K.compatibleContourSourceOnlyBaseMark_metric compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W bank side u v
  have speed := (K.compatibleWholeMap_edist_bank compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W b u v).trans
      ((T).pairedFolding.edist_directedBoundaryPath_eq_length b u v)
  have time := edist_finiteSlotParameterize reverse t
  calc
    _ = edist (Base bank false u) (Base bank false v) := both
    _ = ENNReal.ofReal ((D).boundaryBankLength b) * edist u v := speed
    _ = _ := by
      rw [show edist u v = ENNReal.ofReal t.val from time, mul_comm,
        ← ENNReal.ofReal_mul t.property.1]

/-- Any finite source-only stack slot has its original edge speed, read away from
either endpoint. This applies also to slots with original roof pieces on both sides. -/
theorem compatibleContourSourceOnlyFiniteSlot_arclength
    (e : Edge) (j : Fin ((Stack FiniteBank[e.val,e.property]).length + 1))
    (reverse : Bool) (t : unitInterval) :
    let s : MetricGluing.BankStackSlot Stack := ⟨FiniteBank[e.val,e.property], j⟩
    let u := finiteSlotParameterize reverse (0 : unitInterval)
    let v := finiteSlotParameterize reverse t
    edist (MetricGluing.bankStackLeftCurve Stack Pieces Base Gap s u)
      (MetricGluing.bankStackLeftCurve Stack Pieces Base Gap s v) =
      ENNReal.ofReal (t.val * BankLength[e.val,e.property]) := by
  let bank := FiniteBank[e.val,e.property]
  let s : MetricGluing.BankStackSlot Stack := ⟨bank, j⟩
  let u := finiteSlotParameterize reverse (0 : unitInterval)
  let v := finiteSlotParameterize reverse t
  have original := MetricGluing.bankStackLeftCurve_metric Stack Pieces Base Gap
    (K.compatibleContourSourceOnlyBaseMark_metric compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W)
    (K.compatibleContourSourceOnlyGapMark_metric compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models) s u v
  exact original.trans
    (K.compatibleContourSourceOnlyFiniteRoofBank_arclength compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W e false reverse t)

/-- The named times of a finite bank-radius fan can all be read away from their
particular end, with the original speed and both dependent parameters preserved. -/
theorem compatibleContourSourceOnlyCyclicFiniteSlots_parameterize
    {n : ℕ} (H : MetricGluing.BankStackCyclicClass Pieces Stack Base Gap n)
    (finite_slots : ∀ k, ∃ (e : Edge) (reverse : Bool)
      (j : Fin ((Stack FiniteBank[e.val,e.property]).length + 1)),
      H.time k = ⟨⟨FiniteBank[e.val,e.property], j⟩, finiteSlotParameterize reverse 0⟩) :
    ∃ (parameterize : ∀ j, unitInterval ≃ ParamAt (H.time j).1.1)
      (length : Fin (n + 1) → ℝ),
      (∀ i, 0 < length i) ∧
      (∀ i, parameterize i 0 = (H.time i).2) ∧
      ∀ i (t : unitInterval),
        edist (LeftCurve (H.time i).1 (parameterize i 0))
          (LeftCurve (H.time i).1 (parameterize i t)) =
          ENNReal.ofReal (t.val * length i) := by
  have per_time (s : Time) (finite : ∃ (e : Edge) (reverse : Bool)
      (j : Fin ((Stack FiniteBank[e.val,e.property]).length + 1)),
      s = ⟨⟨FiniteBank[e.val,e.property], j⟩, finiteSlotParameterize reverse 0⟩) :
      ∃ (u : unitInterval ≃ ParamAt s.1.1) (ℓ : ℝ), 0 < ℓ ∧ u 0 = s.2 ∧
        ∀ t : unitInterval, edist (LeftCurve s.1 (u 0)) (LeftCurve s.1 (u t)) =
          ENNReal.ofReal (t.val * ℓ) := by
    obtain ⟨e, reverse, j, rfl⟩ := finite
    exact ⟨finiteSlotParameterize reverse, BankLength[e.val,e.property],
      (D).boundaryBankLength_pos _, rfl,
      K.compatibleContourSourceOnlyFiniteSlot_arclength compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W models e j reverse⟩
  choose u length positive origin arclength using fun j => per_time (H.time j) (finite_slots j)
  exact ⟨u, length, positive, origin, arclength⟩

local notation "OrientedSlot" => (Σ e : Edge,
  Fin (List.length (Stack FiniteBank[Subtype.val e,Subtype.property e]) + 1) × Bool)

/-- A finite slot determined by its original edge, slot number, and starting end
keeps that explicit label at every arclength parameter. -/
theorem compatibleContourSourceOnlyCyclicFiniteSlots_trace_parameters
    {n : ℕ} (H : MetricGluing.BankStackCyclicClass Pieces Stack Base Gap n)
    (named : Fin (n + 1) → OrientedSlot)
    (origin : ∀ i, let q := named i
      H.time i = ⟨⟨FiniteBank[q.1.val,q.1.property], q.2.1⟩, finiteSlotParameterize q.2.2 0⟩) :
    let length (i : Fin (n + 1)) := BankLength[(named i).1.val,(named i).1.property]
    ∃ parameterize : ∀ i, unitInterval ≃ ParamAt (H.time i).1.1,
      (∀ i (t : unitInterval), let q := named i
        (⟨(H.time i).1, parameterize i t⟩ : Time) =
          ⟨⟨FiniteBank[q.1.val,q.1.property], q.2.1⟩, finiteSlotParameterize q.2.2 t⟩) ∧
      (∀ i, parameterize i 0 = (H.time i).2) ∧
      ∀ i (t : unitInterval),
        edist (LeftCurve (H.time i).1 (parameterize i 0))
          (LeftCurve (H.time i).1 (parameterize i t)) =
          ENNReal.ofReal (t.val * length i) := by
  have at_time (s : Time) (q : OrientedSlot)
      (same : s = ⟨⟨FiniteBank[q.1.val,q.1.property], q.2.1⟩, finiteSlotParameterize q.2.2 0⟩) :
      ∃ f : unitInterval ≃ ParamAt s.1.1,
        (∀ t : unitInterval, (⟨s.1, f t⟩ : Time) =
          ⟨⟨FiniteBank[q.1.val,q.1.property], q.2.1⟩, finiteSlotParameterize q.2.2 t⟩) ∧
        f 0 = s.2 ∧
        ∀ t : unitInterval, edist (LeftCurve s.1 (f 0)) (LeftCurve s.1 (f t)) =
          ENNReal.ofReal (t.val * BankLength[q.1.val,q.1.property]) := by
    subst s
    exact ⟨finiteSlotParameterize q.2.2, fun _ => rfl, rfl,
      K.compatibleContourSourceOnlyFiniteSlot_arclength compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W models q.1 q.2.1 q.2.2⟩
  choose parameterize trace at_zero metric using fun i => at_time (H.time i) (named i) (origin i)
  exact ⟨parameterize, trace, at_zero, metric⟩

end Unfoldings.ConvexRoof
