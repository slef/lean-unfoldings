module

public import Unfoldings.Roof.CompatibleContourSourceOnlyLeaf
public import Unfoldings.Roof.CompatibleContourSourceOnlyLabels
public import Unfoldings.Roof.CompatibleContourSourceOnlyGapVertexMarks
public import Unfoldings.Metric.BankStackAddressPredicate
public import Unfoldings.Metric.BankStackIncidentSlots

/-! The actual source-only class at a positive leaf has its two literal intrinsic points. -/

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

local instance sourceOnlyLeafClassesIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlyLeafClassesWholeFintype : Fintype W.Index := W.finiteIndex

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
local notation "BankAt[" e "]" => K.compatibleContourSourceBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "MovedAt[" e "]" => K.compatibleContourSourceOnlyBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "SourceOf[" e "]" => TriangleComplex.positiveContourVertex D Selection contour e
local notation "FirstEdge[" e "]" => (Sum.inl
  (Subtype.mk SourceOf[e] (TriangleComplex.positiveContourVertex_nonroot D Selection contour e)) :
    Attachment)
local notation "RoofPoint[" e "]" => (Sigma.mk none (Base FirstEdge[e] false 0) :
  MetricGluing.Total Pieces)
local notation "GapPoint[" e "]" => (Sigma.mk (some e)
  (BankGapModel.edgePoint (models e) false 0 0) :
  MetricGluing.Total Pieces)
local notation "L" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Rgt" => MetricGluing.bankStackRight Pieces Stack Base Gap

/-- No other original attachment reaches the roof copy at a childless positive source. -/
theorem compatibleContourSourceOnlyLeaf_base_address (event : Event)
    (childless : ∀ v ∉ (Fcut).parents.roots, (Fcut).parents.parent v ≠ SourceOf[event])
    (bank : Attachment) (side : Bool) (t : ParamAt bank)
    (equal : Base bank side t = Base FirstEdge[event] false 0) :
    (⟨bank, t⟩ : Σ b : Attachment, ParamAt b) = ⟨FirstEdge[event], 0⟩ := by
  let v := SourceOf[event]
  let nonroot := (D).positiveContourVertex_nonroot Selection contour event
  obtain ⟨_, w, original, below, _, copies⟩ :=
    K.compatibleContourSourceOnlyLeaf_roof_fan compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W event nonroot childless
  have same := equal.trans (copies false)
  let originalVertex := (D).vertexForgetCuts (Set.subset_univ (Fcut).retain)
  cases bank with
  | inr e =>
    exact (K.compatibleContourRoofVertex_ne_tailMark compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W w below e side t same).elim
  | inl e =>
    have endpoint := (K.compatibleContourRoofVertex_eq_parentMark_iff compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W
      w below e side t).mp same
    rcases endpoint with ⟨rfl, hw⟩ | ⟨rfl, hw⟩
    · have first := (D).contourParentBank_start Selection contour (Fcut).boundary_roots
        starts e.val e.property side
      have original_eq : e.val = v :=
        first.symm.trans ((congrArg originalVertex hw).symm.trans original)
      have e_eq : e = ⟨v, nonroot⟩ := Subtype.ext original_eq
      subst e
      rfl
    · have last := (D).contourParentBank_finish Selection contour (Fcut).boundary_roots
        starts e.val e.property side
      have original_eq : (Fcut).parents.parent e.val = v :=
        last.symm.trans ((congrArg originalVertex hw).symm.trans original)
      exact (childless e.val e.property original_eq).elim

local notation "Banks" => MetricGluing.bankSeams L Rgt
local notation "Addr" => MetricGluing.BankStackAddress (G := Event) (Parameter := ParamAt)
local notation "AddrPoint" => MetricGluing.bankStackAddressPoint Stack Pieces Base Gap
local notation "Valid" => MetricGluing.BankStackAddressValid Stack
local notation "EndAt" => MetricGluing.bankStackEndpoint Stack Pieces Base Gap
local notation "EndAddr" => MetricGluing.bankStackEndpointAddress (Parameter := ParamAt) Stack

/-- An actual seam endpoint at the positive leaf keeps its named source edge and time zero. -/
theorem compatibleContourSourceOnlyLeaf_endpoint_iff
    (event : Event) (g : OrientedBankGap BankAt[event] MovedAt[event])
    (childless : ∀ v ∉ (Fcut).parents.roots, (Fcut).parents.parent v ≠ SourceOf[event])
    (side : Bool) (slot : MetricGluing.BankStackSlot Stack) (t : ParamAt slot.1) :
    (EndAt side slot t = RoofPoint[event] ∨ EndAt side slot t = GapPoint[event]) ↔
      (⟨slot.1, t⟩ : Σ f : Attachment, ParamAt f) = ⟨FirstEdge[event], 0⟩ := by
  let b := FirstEdge[event]
  let atStart : Σ f : Attachment, ParamAt f := ⟨b, 0⟩
  let pair (y : MetricGluing.Total Pieces) := y = RoofPoint[event] ∨ y = GapPoint[event]
  have nonroot := (D).positiveContourVertex_nonroot Selection contour event
  obtain ⟨one, w, _, _, _, copies⟩ :=
    K.compatibleContourSourceOnlyLeaf_roof_fan compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W event nonroot childless
  change Stack b = [event] at one
  have self : event ∈ Stack b := by rw [one]; exact List.mem_cons_self
  have tip (side : Bool) : Gap b event self side 0 = (models event).edgePoint false 0 0 :=
    K.compatibleContourSourceOnlyGapMark_at_source compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts models event g self side
  have roof (side : Bool) : Base b side 0 = Base b false 0 :=
    (copies side).trans (copies false).symm
  have address (a : Addr) (valid : Valid a) (near : pair (AddrPoint a valid)) :
      (⟨a.1, a.2.2.2⟩ : Σ f : Attachment, ParamAt f) = atStart := by
    obtain ⟨f, tag, side, t⟩ := a
    cases tag with
    | none =>
      rcases near with same | impossible
      · exact K.compatibleContourSourceOnlyLeaf_base_address compact nonempty R no_boundary
          level higher M positive inner_disk beta acute contour starts W event childless f side
          t (eq_of_heq (Sigma.mk.inj same).2)
      · cases congrArg Sigma.fst impossible
    | some other =>
      rcases near with impossible | same
      · cases congrArg Sigma.fst impossible
      · have named : other = event := Option.some.inj (congrArg Sigma.fst same)
        subst other
        exact K.compatibleContourSourceOnlyGapMark_eq_source_attachment compact nonempty R
          no_boundary level higher M positive inner_disk beta acute contour starts models
          event g self f valid side t (eq_of_heq (Sigma.mk.inj same).2)
  have at_address (a : Addr) (valid : Valid a)
      (key : (⟨a.1, a.2.2.2⟩ : Σ f : Attachment, ParamAt f) = atStart) :
      pair (AddrPoint a valid) := by
    obtain ⟨f, tag, side, t⟩ := a
    have location : f = b := congrArg Sigma.fst key
    subst f
    have time : t = 0 := eq_of_heq (Sigma.mk.inj key).2
    subst t
    cases tag with
    | none => exact Or.inl (congrArg (Sigma.mk none) (roof side))
    | some other =>
      have member : other ∈ Stack b := valid
      have named : other = event := by simpa only [one, List.mem_singleton] using member
      subst other
      exact Or.inr (congrArg (Sigma.mk (some event)) (tip side))
  have endpoint (side : Bool) (slot : MetricGluing.BankStackSlot Stack) (t : ParamAt slot.1) :
      pair (EndAt side slot t) ↔ (⟨slot.1, t⟩ : Σ f : Attachment, ParamAt f) = atStart := by
    have mark := MetricGluing.bankStackAddressPoint_endpoint Stack Pieces Base Gap side slot t
    have key := MetricGluing.bankStackEndpointAddress_parameter
      (Parameter := ParamAt) Stack side slot t
    let a := EndAddr side slot t
    let valid : Valid a := MetricGluing.bankStackEndpointAddress_valid Stack side slot t
    constructor
    · intro near
      exact key.symm.trans (address a valid (mark.symm ▸ near))
    · intro same
      exact mark ▸ at_address a valid (key.trans same)
  exact endpoint side slot t

/-- The two intrinsic points at a positive leaf are the only members of its actual class. -/
theorem compatibleContourSourceOnlyLeaf_eqvGen_pair
    (event : Event) (g : OrientedBankGap BankAt[event] MovedAt[event])
    (childless : ∀ v ∉ (Fcut).parents.roots, (Fcut).parents.parent v ≠ SourceOf[event])
    (x : MetricGluing.Total Pieces) :
    Relation.EqvGen Banks RoofPoint[event] x ↔
      x = RoofPoint[event] ∨ x = GapPoint[event] := by
  let b := FirstEdge[event]
  let atStart : Σ f : Attachment, ParamAt f := ⟨b, 0⟩
  let pair (y : MetricGluing.Total Pieces) := y = RoofPoint[event] ∨ y = GapPoint[event]
  have nonroot := (D).positiveContourVertex_nonroot Selection contour event
  have one : Stack b = [event] := (D).contourSavedGapStack_leaf Selection contour
    (Fcut).boundary_roots starts event nonroot childless
  have endpoint (side : Bool) (slot : MetricGluing.BankStackSlot Stack) (t : ParamAt slot.1) :
      pair (EndAt side slot t) ↔ (⟨slot.1, t⟩ : Σ f : Attachment, ParamAt f) = atStart :=
    K.compatibleContourSourceOnlyLeaf_endpoint_iff compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models event g childless side slot t
  have closed (a c : MetricGluing.Total Pieces) (joined : Banks a c) : pair a ↔ pair c := by
    obtain ⟨slot, t, rfl, rfl⟩ := joined
    exact (endpoint false slot t).trans (endpoint true slot t).symm
  have invariant {a c : MetricGluing.Total Pieces} (path : Relation.EqvGen Banks a c) :
      pair a ↔ pair c := by
    induction path with
    | rel a c h => exact closed a c h
    | refl a => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  constructor
  · intro path
    exact (invariant path).mp (Or.inl rfl)
  · rintro (rfl | rfl)
    · exact Relation.EqvGen.refl _
    · let slot : MetricGluing.BankStackSlot Stack := ⟨b, 0⟩
      have left : L slot 0 = RoofPoint[event] :=
        MetricGluing.bankStackLeft_first Pieces Stack Base Gap b 0
      have right : Rgt slot 0 = GapPoint[event] := by
        rcases (endpoint true slot 0).mpr rfl with wrong | correct
        · let i : Fin ((Stack b).length) :=
            ⟨0, by simp only [one, List.length_cons, Nat.zero_lt_succ]⟩
          have selected := MetricGluing.bankStackRight_at Pieces Stack Base Gap b i 0
          have impossible := congrArg Sigma.fst (selected.symm.trans wrong)
          cases impossible
        · exact correct
      exact Relation.EqvGen.rel _ _ ⟨slot, 0, left.symm, right.symm⟩

/-- Exactly the original roof corner and gap tip represent the leaf in the actual metric. -/
theorem compatibleContourSourceOnlyLeaf_point_eq_iff
    (geometry : ∀ event : Event, OrientedBankGap BankAt[event] MovedAt[event])
    (event : Event)
    (childless : ∀ v ∉ (Fcut).parents.roots, (Fcut).parents.parent v ≠ SourceOf[event])
    (x : MetricGluing.Total Pieces) :
    MetricGluing.point Pieces Banks RoofPoint[event] = MetricGluing.point Pieces Banks x ↔
      x = RoofPoint[event] ∨ x = GapPoint[event] := by
  have exactness := K.compatibleContourSourceOnlyGraft_exact compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W models geometry
  have same := K.compatibleContourSourceOnlyLeaf_eqvGen_pair compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W models event (geometry event)
    childless x
  exact ⟨fun equal => same.mp (exactness _ _ equal),
    fun alternative => MetricGluing.point_eq_of_eqvGen Pieces (same.mpr alternative)⟩

/-- A whole neighborhood of the positive leaf lifts to just its two original piece balls. -/
theorem compatibleContourSourceOnlyLeaf_piece_ball_cover
    (geometry : ∀ event : Event, OrientedBankGap BankAt[event] MovedAt[event])
    (event : Event)
    (childless : ∀ v ∉ (Fcut).parents.roots, (Fcut).parents.parent v ≠ SourceOf[event]) :
    ∃ r > 0, ∀ b : MetricGluing.Total Pieces,
      edist (MetricGluing.point Pieces Banks RoofPoint[event])
        (MetricGluing.point Pieces Banks b) < ENNReal.ofReal r →
      ∃ c : Pieces b.1, (⟨b.1, c⟩ = RoofPoint[event] ∨ ⟨b.1, c⟩ = GapPoint[event]) ∧
        edist c b.2 < ENNReal.ofReal r := by
  obtain ⟨r, rpos, cover⟩ := K.compatibleContourSourceOnlyGraft_piece_ball_cover compact
    nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W
    models geometry RoofPoint[event]
  refine ⟨r, rpos, ?_⟩
  intro b near
  obtain ⟨c, related, close⟩ := cover r rpos le_rfl b near
  exact ⟨c, (K.compatibleContourSourceOnlyLeaf_eqvGen_pair compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W models event (geometry event)
    childless ⟨b.1, c⟩).mp related, close⟩

local notation "Curve" => MetricGluing.bankStackLeftCurve Stack Pieces Base Gap

/-- Every nearby seam at a positive leaf approaches its original time-zero mark
on one of the two actual source edge slots. -/
theorem compatibleContourSourceOnlyLeaf_near_slot
    (geometry : ∀ event : Event, OrientedBankGap BankAt[event] MovedAt[event])
    (event : Event)
    (childless : ∀ v ∉ (Fcut).parents.roots, (Fcut).parents.parent v ≠ SourceOf[event]) :
    ∃ r > 0, ∀ slot : MetricGluing.BankStackSlot Stack, ∀ t : ParamAt slot.1,
      edist (MetricGluing.point Pieces Banks RoofPoint[event])
        (MetricGluing.point Pieces Banks (L slot t)) < ENNReal.ofReal r →
      ∃ u : ParamAt slot.1, (⟨slot.1, u⟩ : Σ f : Attachment, ParamAt f) = ⟨FirstEdge[event], 0⟩ ∧
        edist (Curve slot u) (Curve slot t) < ENNReal.ofReal r := by
  have members := K.compatibleContourSourceOnlyLeaf_eqvGen_pair compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models event (geometry event)
    childless
  have finite (i : Option Event) :
      {q : Pieces i | Relation.EqvGen Banks RoofPoint[event] ⟨i, q⟩}.Finite := by
    have two := (Set.finite_singleton RoofPoint[event]).union (Set.finite_singleton GapPoint[event])
    have injective : Function.Injective
        (fun q : Pieces i => (⟨i, q⟩ : MetricGluing.Total Pieces)) :=
      fun _ _ h => eq_of_heq (Sigma.mk.inj h).2
    apply (two.preimage injective.injOn).subset
    intro q h
    exact (members ⟨i, q⟩).mp h
  obtain ⟨ε, epspos, cover⟩ := K.compatibleContourSourceOnlyGraft_piece_ball_cover compact
    nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W
    models geometry RoofPoint[event]
  obtain ⟨r, rpos, same⟩ := MetricGluing.exists_bankStack_incident_slot_radius Pieces Stack Base Gap
    RoofPoint[event] finite
    (K.compatibleContourSourceOnlyBaseMark_isClosedEmbedding compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W)
    (K.compatibleContourSourceOnlyGapMark_isClosedEmbedding compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts models)
    epspos cover
  refine ⟨r, rpos, ?_⟩
  intro slot t near
  obtain ⟨u, original, close⟩ := same slot t near
  have endpoint := K.compatibleContourSourceOnlyLeaf_endpoint_iff compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W models
    event (geometry event) childless false slot u
  exact ⟨u, endpoint.mp ((members _).mp original), close⟩

end Unfoldings.ConvexRoof
