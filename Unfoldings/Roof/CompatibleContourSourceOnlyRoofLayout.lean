module

public import Unfoldings.Roof.CompatibleContourSourceOnlyGraftDevelopment
public import Unfoldings.Roof.CompatibleCutClosed

/-! Restrict the global graft layout while tracking the restored roof points. -/

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

local instance sourceOnlyRoofLayoutIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlyRoofLayoutWholeFintype : Fintype W.Index := W.finiteIndex

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
local notation "LengthAt[" e "]" => TriangleComplex.positiveContourBankLength D Selection contour e
local notation "BankAt[" e "]" => K.compatibleContourSourceBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "Graft" => K.compatibleContourSourceOnlyGraft compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "L" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Rgt" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams L Rgt

local notation "Point" => MetricGluing.point Pieces Banks
local notation "Phys" => K.compatibleContourPhysicalAttachmentPoint compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W

local notation "Visit[" j "]" => TriangleComplex.contourOriginalVertex D Selection contour j
local notation "Addr" => MetricGluing.BankStackAddress (G := Event) (Parameter := ParamAt)

include geometry

set_option maxHeartbeats 2500000 in
-- The constructed collapse names all seam endpoints in the dependent bank types.
/-- The developed roof is locally isometric off the cuts, and coincidence in
the development implies coincidence after restoring the original spatial placement. -/
theorem compatibleContourSourceOnlyGraft_exists_roof_layout
    (convex : Convex ℝ slopes) (ends : Visit[Fin.last contour.length] ∈ (Fcut).parents.roots)
    (strict : ∀ (e : Event) (k : Fin LengthAt[e]), let B := BankAt[e]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ)) :
    ∃ layout : W.Cut → Plane, Continuous layout ∧
      (∀ x y, layout x = layout y →
        (W.partition.restoreCut R.carrier x).val = (W.partition.restoreCut R.carrier y).val) ∧
      ∀ x : W.Cut, Cap.horizontal (W.partition.restoreCut R.carrier x).val ∉ R.carrier →
        ∃ r > 0, Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => layout y.val) := by
  obtain ⟨d, rigid, onto⟩ := K.compatibleContourSourceOnlyGraft_exists_surjective_isometry
    compact nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W
    geometry convex ends strict
  obtain ⟨f, proper, roof, gap⟩ := K.compatibleContourSourceOnlyGraft_exists_proper_collapse
    compact nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W
    models geometry (fun _ => rfl)
  let A : Graft ≃ᵢ Plane :=
    ⟨Equiv.ofBijective d ⟨rigid.injective, onto⟩, rigid⟩
  let layout (x : W.Cut) := d (Point ⟨none, x⟩)
  refine ⟨layout, rigid.continuous.comp (MetricGluing.of_lipschitz Pieces Banks none).continuous,
    ?_, ?_⟩
  · intro x y equal
    exact (roof x).symm.trans ((congrArg f (rigid.injective equal)).trans (roof y))
  intro x outside
  have attached {b c : MetricGluing.Total Pieces} (joined : Banks b c) :
      Cap.horizontal (f (Point b)) ∈ R.carrier := by
    obtain ⟨slot, t, rfl, rfl⟩ := joined
    let a : Addr := MetricGluing.bankStackEndpointAddress Stack false slot t
    have value := K.compatibleContourSourceOnlyCollapse_mark_horizontal compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W models
      geometry f roof gap a (MetricGluing.bankStackEndpointAddress_valid Stack false slot t)
    rw [MetricGluing.bankStackAddressPoint_endpoint Stack Pieces Base Gap false slot t] at value
    have address := MetricGluing.bankStackEndpointAddress_parameter Stack false slot t
    have physical : Cap.horizontal (f (Point (L slot t))) = Phys slot.1 t :=
      value.trans (congrArg (fun p : Σ b : Attachment, ParamAt b => Phys p.1 p.2) address)
    rw [physical]
    rcases slot with ⟨bank, i⟩
    cases bank with
    | inl v =>
      exact K.compatibleContourParentMark_carrier compact nonempty R no_boundary level higher
        M positive inner_disk beta acute contour starts W v.val v.property false t
    | inr v =>
      exact K.compatibleContourTerminalMark_carrier compact nonempty R no_boundary level higher
        M positive inner_disk beta acute contour starts W v false t
  let p (y : Plane) := Cap.horizontal (f (A.symm y))
  have cont : Continuous p := Cap.horizontalCLM.continuous.comp
    (proper.continuous.comp A.symm.continuous)
  let U := p ⁻¹' (R.carrier)ᶜ
  have open_U : IsOpen U := R.isClosed_carrier.isOpen_compl.preimage cont
  have in_U : layout x ∈ U := by
    change Cap.horizontal (f (A.symm (A (Point ⟨none, x⟩)))) ∉ R.carrier
    rw [A.symm_apply_apply, roof]
    exact outside
  obtain ⟨δ, δpos, free⟩ := Metric.isOpen_iff.mp open_U (layout x) in_U
  have distant (b c : MetricGluing.Total Pieces) (joined : Banks b c) :
      ENNReal.ofReal δ ≤ edist (Point ⟨none, x⟩) (Point b) := by
    apply le_of_not_gt
    intro near
    have close := near
    rw [← A.isometry.edist_eq (Point ⟨none, x⟩) (Point b), edist_comm, edist_dist] at close
    have in_ball : A (Point b) ∈ Metric.ball (layout x) δ :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp close
    have hn := free in_ball
    change Cap.horizontal (f (A.symm (A (Point b)))) ∉ R.carrier at hn
    rw [A.symm_apply_apply] at hn
    exact hn (attached joined)
  refine ⟨δ / 3, div_pos δpos (by norm_num), ?_⟩
  exact rigid.comp (MetricGluing.of_isometry_on_ball_of_no_seams Pieces Banks none x δpos distant)

end Unfoldings.ConvexRoof
