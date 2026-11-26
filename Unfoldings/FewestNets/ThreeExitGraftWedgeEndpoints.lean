module

public import Unfoldings.FewestNets.ThreeExitRoofVertexMarks
public import Unfoldings.FewestNets.ThreeExitGraftStrictFiber
public import Unfoldings.Metric.BankStackEndpointExistence
public import Unfoldings.Metric.BankStackAdjacentGaps


/-! Exact seam times on the sides of a roof wedge. -/

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

local instance graftWedgeEndpointsIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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
local notation "EndAt" => MetricGluing.bankStackEndpoint Stack Pieces Base Gap
local notation "Time" => (Σ s : MetricGluing.BankStackSlot Stack, Param (Sigma.fst s))

local notation "Named" => MetricGluing.bankStackEndpointAddress (Parameter := Param) Stack
local notation "Addr" => MetricGluing.BankStackAddress («G» := Event) (Parameter := Param)
local notation "Valid" => MetricGluing.BankStackAddressValid Stack
local notation "Mark" => MetricGluing.bankStackAddressPoint Stack Pieces Base Gap
local notation "SourceOf[" e "]" => TriangleComplex.positiveContourVertex D Selection S.contour e
local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams Left Right
/-- The exact original roof wedge is the left endpoint at the old child’s first
slot and the right endpoint at the new child’s last slot. -/
theorem contourGraftRoofWedge_endpoint_iff
    (old_child new_child : Edge) (j : Fin (S.contour.length + 1))
    (after_old : finRotate (S.contour.length + 1) ((D).contourParentInterval Selection S.contour
      (Fcut).boundary_roots S.starts old_child.val old_child.property).leave = j)
    (before_new : ((D).contourParentInterval Selection S.contour (Fcut).boundary_roots S.starts
      new_child.val new_child.property).enter = j)
    (nonroot : (D).contourOriginalVertex Selection S.contour j ∉ (Fcut).parents.roots)
    (flag : Bool) (s : Time) :
    let w := (D).boundaryEndVertex Retain (S.contour.cycle.point j)
    let old_bank := FiniteBank[old_child.val,old_child.property]
    let new_bank := FiniteBank[new_child.val,new_child.property]
    let first : Time := ⟨⟨old_bank, 0⟩, 1⟩
    let last : Time := ⟨⟨new_bank, Fin.last (Stack new_bank).length⟩, 1⟩
    EndAt flag s.1 s.2 = ⟨none, Map ((D).vertexPoint Retain w)⟩ ↔
      (flag = false ∧ s = first) ∨ (flag = true ∧ s = last) := by
  let w := (D).boundaryEndVertex Retain (S.contour.cycle.point j)
  let x := Map ((D).vertexPoint Retain w)
  let old_bank := FiniteBank[old_child.val,old_child.property]
  let new_bank := FiniteBank[new_child.val,new_child.property]
  let first : Time := ⟨⟨old_bank, 0⟩, 1⟩
  let last : Time := ⟨⟨new_bank, Fin.last (Stack new_bank).length⟩, 1⟩
  have first_name : Named false first.1 first.2 = ⟨old_bank, none, false, 1⟩ := by
    simp [first, MetricGluing.bankStackEndpointAddress, MetricGluing.bankStackLeftAddress]
  have last_name : Named true last.1 last.2 = ⟨new_bank, none, true, 1⟩ := by
    simp [last, MetricGluing.bankStackEndpointAddress, MetricGluing.bankStackRightAddress]
  have name (bank : Attachment) (side : Bool) (t : Param bank) :=
    L.contourRoofWedge_baseMark_iff S old_child new_child j after_old before_new
      nonroot bank side t
  constructor
  · intro at_center
    have nodup := contourGraft_stack_nodup S
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
        · exact Or.inl (congrArg (fun z : Σ b : Attachment, Param b =>
            (⟨z.1, none, false, z.2⟩ : Addr)) times)
        · exact Or.inr (congrArg (fun z : Σ b : Attachment, Param b =>
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

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
