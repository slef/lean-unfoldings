module

public import Unfoldings.FewestNets.ThreeExitGraftMarkMetrics
public import Unfoldings.Roof.CompatibleContourSourceOnlyFiniteSlotRadii


/-! Original finite seam speeds for each radius in a vertex chart. -/

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

local instance graftVertexRadiiIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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
local notation "BankLength[" v "," h "]" => TriangleComplex.boundaryBankLength D
  (TriangleComplex.contourParentBank D Selection S.contour (PotentialCutForest.boundary_roots Fcut)
    S.starts v h false)
local notation "LeftCurve" => bankStackLeftCurve Stack Pieces Base Gap
local notation "Time" => (Σ s : MetricGluing.BankStackSlot Stack, Param (Sigma.fst s))

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
theorem contourGraftFiniteRoofBank_arclength
    (e : Edge) (side reverse : Bool) (t : unitInterval) :
    let b := FiniteBank[e.val,e.property]
    edist (Base b side (finiteSlotParameterize reverse 0))
      (Base b side (finiteSlotParameterize reverse t)) =
      ENNReal.ofReal (t.val * BankLength[e.val,e.property]) := by
  let (a : Attachment) : MetricSpace (Param a) := contourAttachmentMetric S a
  let bank := FiniteBank[e.val,e.property]
  let u := finiteSlotParameterize reverse (0 : unitInterval)
  let v := finiteSlotParameterize reverse t
  let b := (D).contourParentBank Selection S.contour (Fcut).boundary_roots S.starts e.val e.property false
  have both := L.edist_contourBaseMark_sides S bank side u v
  have speed := (L.fineMeshWholeMap_edist_bank S.higher b u v).trans
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
theorem contourGraftFiniteSlot_arclength
    (e : Edge) (j : Fin ((Stack FiniteBank[e.val,e.property]).length + 1))
    (reverse : Bool) (t : unitInterval) :
    let s : MetricGluing.BankStackSlot Stack := ⟨FiniteBank[e.val,e.property], j⟩
    let u := finiteSlotParameterize reverse (0 : unitInterval)
    let v := finiteSlotParameterize reverse t
    edist (MetricGluing.bankStackLeftCurve Stack Pieces Base Gap s u)
      (MetricGluing.bankStackLeftCurve Stack Pieces Base Gap s v) =
      ENNReal.ofReal (t.val * BankLength[e.val,e.property]) := by
  let (a : Attachment) : MetricSpace (Param a) := contourAttachmentMetric S a
  let bank := FiniteBank[e.val,e.property]
  let s : MetricGluing.BankStackSlot Stack := ⟨bank, j⟩
  let u := finiteSlotParameterize reverse (0 : unitInterval)
  let v := finiteSlotParameterize reverse t
  have original := MetricGluing.bankStackLeftCurve_metric Stack Pieces Base Gap
    (L.edist_contourBaseMark_sides S)
    (L.edist_contourGapMark_eq_base S) s u v
  exact original.trans
    (L.contourGraftFiniteRoofBank_arclength S e false reverse t)

/-- The named times of a finite bank-radius fan can all be read away from their
particular end, with the original speed and both dependent parameters preserved. -/
theorem contourGraftCyclicFiniteSlots_parameterize
    {n : ℕ} (H : MetricGluing.BankStackCyclicClass Pieces Stack Base Gap n)
    (finite_slots : ∀ k, ∃ (e : Edge) (reverse : Bool)
      (j : Fin ((Stack FiniteBank[e.val,e.property]).length + 1)),
      H.time k = ⟨⟨FiniteBank[e.val,e.property], j⟩, finiteSlotParameterize reverse 0⟩) :
    ∃ (parameterize : ∀ j, unitInterval ≃ Param (H.time j).1.1)
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
      ∃ (u : unitInterval ≃ Param s.1.1) (ℓ : ℝ), 0 < ℓ ∧ u 0 = s.2 ∧
        ∀ t : unitInterval, edist (LeftCurve s.1 (u 0)) (LeftCurve s.1 (u t)) =
          ENNReal.ofReal (t.val * ℓ) := by
    obtain ⟨e, reverse, j, rfl⟩ := finite
    exact ⟨finiteSlotParameterize reverse, BankLength[e.val,e.property],
      (D).boundaryBankLength_pos _, rfl,
      L.contourGraftFiniteSlot_arclength S e j reverse⟩
  choose u length positive origin arclength using fun j => per_time (H.time j) (finite_slots j)
  exact ⟨u, length, positive, origin, arclength⟩

local notation "OrientedSlot" => (Σ e : Edge,
  Fin (List.length (Stack FiniteBank[Subtype.val e,Subtype.property e]) + 1) × Bool)

/-- A finite slot determined by its original edge, slot number, and starting end
keeps that explicit label at every arclength parameter. -/
theorem contourGraftCyclicFiniteSlots_trace_parameters
    {n : ℕ} (H : MetricGluing.BankStackCyclicClass Pieces Stack Base Gap n)
    (named : Fin (n + 1) → OrientedSlot)
    (origin : ∀ i, let q := named i
      H.time i = ⟨⟨FiniteBank[q.1.val,q.1.property], q.2.1⟩, finiteSlotParameterize q.2.2 0⟩) :
    let length (i : Fin (n + 1)) := BankLength[(named i).1.val,(named i).1.property]
    ∃ parameterize : ∀ i, unitInterval ≃ Param (H.time i).1.1,
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
      ∃ f : unitInterval ≃ Param s.1.1,
        (∀ t : unitInterval, (⟨s.1, f t⟩ : Time) =
          ⟨⟨FiniteBank[q.1.val,q.1.property], q.2.1⟩, finiteSlotParameterize q.2.2 t⟩) ∧
        f 0 = s.2 ∧
        ∀ t : unitInterval, edist (LeftCurve s.1 (f 0)) (LeftCurve s.1 (f t)) =
          ENNReal.ofReal (t.val * BankLength[q.1.val,q.1.property]) := by
    subst s
    exact ⟨finiteSlotParameterize q.2.2, fun _ => rfl, rfl,
      L.contourGraftFiniteSlot_arclength S q.1 q.2.1 q.2.2⟩
  choose parameterize trace at_zero metric using fun i => at_time (H.time i) (named i) (origin i)
  exact ⟨parameterize, trace, at_zero, metric⟩

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
