module

public import Unfoldings.Roof.CompatibleContourSelectedSlotsGraft
public import Unfoldings.Roof.CompatibleContourTerminalJoinEndpoints
public import Unfoldings.Metric.ForgetChartTransport

/-! At the rim join, only the two consecutive bank slots remain locally. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof

open MetricGluing

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

local notation "inside" => K.compatible_section_interior compact nonempty R level higher M

local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance contourTerminalJoinExcisionMeshFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut

local notation "BankAt[" q "," h "," e "]" =>
  K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e
local notation "OpenedAt[" q "," h "," e "]" =>
  K.compatibleContourOpenedBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e

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
      (K.compatibleContourOpenedBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance contourTerminalJoinExcisionWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Pieces" => K.compatibleContourGraftPiece compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour starts W models
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Base" => K.compatibleContourBaseMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Gap" => K.compatibleContourGapMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models

local notation "Index" => K.compatibleContourCellIndex compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Cells" => K.compatibleContourCells compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Inner" => K.compatibleContourCellInner compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Coordinates" => K.compatibleContourCellCoordinates compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "Seams" => K.compatibleContourClosedSeams compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts W models
local notation "Banks" => MetricGluing.bankSeams (MetricGluing.bankStackLeft Pieces Stack Base Gap)
  (MetricGluing.bankStackRight Pieces Stack Base Gap)

local notation "Raw" => MetricGluing.NestedCell (fun i j => Cells i j)
local notation "Original" => MetricGluing.mappedNestedPoint Cells Inner Coordinates
local notation "BankSeams" => K.compatibleContourBankClosedSeams compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "LP" => MetricGluing.bankStackLeftPiece Stack Pieces Base Gap

local notation "RP" => MetricGluing.bankStackRightPiece Stack Pieces Base Gap
local notation "LC" => MetricGluing.bankStackLeftCurve Stack Pieces Base Gap
local notation "RC" => MetricGluing.bankStackRightCurve Stack Pieces Base Gap
local notation "Internal" => K.compatibleContourInternalClosedSeams compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "ParamAt[" b "]" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute b


local notation "Edge" => TriangleComplex.ContourTerminalEdge D Selection
local notation "Child[" e "]" => (Subtype.mk (Subtype.val e) (And.left (Subtype.property e)))
local notation "TailSlot[" e "," i "]" => (Sigma.mk (Sum.inr e) i : BankStackSlot Stack)
local notation "LastSlot[" e "," i "]" => (Sigma.mk (Sum.inl Child[e]) i : BankStackSlot Stack)
local notation "LeftAt" => bankStackLeft Pieces Stack Base Gap
local notation "RightAt" => bankStackRight Pieces Stack Base Gap
local notation "Keep[" e "," i "]" => ({LastSlot[e,i],TailSlot[e,i]} : Set (BankStackSlot Stack))
local notation "SelectedLeft[" keep "]" => fun (slot : Subtype (keep :
    Set (BankStackSlot Stack))) (t : ParamAt[Sigma.fst (Subtype.val slot)]) =>
      LeftAt (Subtype.val slot) t
local notation "SelectedRight[" keep "]" => fun (slot : Subtype (keep :
    Set (BankStackSlot Stack))) (t : ParamAt[Sigma.fst (Subtype.val slot)]) =>
      RightAt (Subtype.val slot) t
local notation "SelectedPoint[" keep "]" => point Pieces
  (bankSeams SelectedLeft[keep] SelectedRight[keep])

private theorem compatibleContourTerminalJoin_incident_slot
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1))
    (a : Total Raw) (center : Original a = LeftAt TailSlot[edge,i] 0)
    (b : (BankSeams).Seam) (incident : (Seams).Incident a (.inr b)) : b.1 ∈ Keep[edge,i] := by
  obtain ⟨p, related, u, equal⟩ := incident
  obtain ⟨s, first, _⟩ := u.property
  have bank_point : Original ⟨(BankSeams).left b, p⟩ = LeftAt b.1 s :=
    (congrArg (fun q => Original ⟨(BankSeams).left b, q⟩) equal.symm).trans
      ((congrArg (Sigma.mk (LP b.1)) first).trans
        (bankStackLeft_curve Stack Pieces Base Gap b.1 s).symm)
  have points := congrArg
    (K.compatibleContourClosedSeamIsometry compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models)
    (point_eq_of_eqvGen Raw related)
  change point Pieces Banks (Original a) =
    point Pieces Banks (Original ⟨(BankSeams).left b, p⟩) at points
  have same : point Pieces Banks (LeftAt b.1 s) = point Pieces Banks (LeftAt TailSlot[edge,i] 0) :=
    (congrArg (point Pieces Banks) bank_point).symm.trans
      (points.symm.trans (congrArg (point Pieces Banks) center))
  rcases K.compatibleContourTerminalJoin_endpoint_parameter_eq compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models geometry edge i
    false b.1 s same with ht | hf
  · exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr (congrArg Sigma.fst ht))
  · exact Set.mem_insert_iff.mpr (Or.inl (congrArg Sigma.fst hf))

private theorem compatibleContourTerminalJoin_representative
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) :
    ∃ a : Total Raw, Original a = LeftAt TailSlot[edge,i] 0 :=
  mappedNestedPoint_surjective Cells Inner Coordinates (LeftAt TailSlot[edge,i] 0)

private theorem compatibleContourTerminalJoin_forgetChart
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1))
    (a : Total Raw) (center : Original a = LeftAt TailSlot[edge,i] 0) :
    let kept := K.compatibleContourKeepBankSlots compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models Keep[edge,i]
    Nonempty (ForgetChart Raw ((Seams).restrict_relation_included kept) a) := by
  let kept := K.compatibleContourKeepBankSlots compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W models Keep[edge,i]
  exact (Seams).exists_forgetChart_restrict kept a
    (K.compatibleContourClosedSeams_finite_classes compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models geometry a) (by
        intro s incident
        cases s with
        | inl internal => trivial
        | inr bank =>
          exact K.compatibleContourTerminalJoin_incident_slot compact nonempty R no_boundary
            level higher M positive inner_disk beta acute contour starts W models geometry
            edge i a center bank incident)

private theorem compatibleContourTerminalJoin_selectedSlots_ball_of_representative
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1))
    (a : Total Raw) (center : Original a = LeftAt TailSlot[edge,i] 0) :
    let x : Total Pieces := LeftAt TailSlot[edge,i] 0
    ∃ (r : ℝ) (rpos : 0 < r),
      ∃ A : Metric.eball (SelectedPoint[Keep[edge,i]] x) (ENNReal.ofReal r) ≃ᵢ
          Metric.eball (point Pieces Banks x) (ENNReal.ofReal r),
        (A ⟨SelectedPoint[Keep[edge,i]] x,
          Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos)⟩).val = point Pieces Banks x := by
  let x : Total Pieces := LeftAt TailSlot[edge,i] 0
  let keep := Keep[edge,i]
  let kept := K.compatibleContourKeepBankSlots compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W models keep
  refine (K.compatibleContourTerminalJoin_forgetChart compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W models geometry edge i a center).elim ?_
  intro C
  let first := K.compatibleContourSelectedSlotsIsometry compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W models keep
  let last := K.compatibleContourClosedSeamIsometry compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W models
  have hf : first (point Raw ((Seams).restrict kept).relation a) = SelectedPoint[keep] x :=
    congrArg SelectedPoint[keep] center
  have hl : last (point Raw (Seams).relation a) = point Pieces Banks x :=
    congrArg (point Pieces Banks) center
  exact ⟨C.radius, C.positive, C.transportBall first last _ _ hf hl,
    C.transportBall_center first last _ _ hf hl⟩

/-- The actual rim join has a whole ball captured by its two adjacent original slots,
with all original intrinsic pieces and coordinates kept. -/
theorem compatibleContourTerminalJoin_selectedSlots_ball
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) :
    let x : Total Pieces := LeftAt TailSlot[edge,i] 0
    ∃ (r : ℝ) (rpos : 0 < r),
      ∃ A : Metric.eball (SelectedPoint[Keep[edge,i]] x) (ENNReal.ofReal r) ≃ᵢ
          Metric.eball (point Pieces Banks x) (ENNReal.ofReal r),
        (A ⟨SelectedPoint[Keep[edge,i]] x,
          Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos)⟩).val = point Pieces Banks x :=
  (K.compatibleContourTerminalJoin_representative compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W models edge i).elim fun a center =>
      K.compatibleContourTerminalJoin_selectedSlots_ball_of_representative compact nonempty R
        no_boundary level higher M positive inner_disk beta acute contour starts W models
        geometry edge i a center

end Unfoldings.ConvexRoof
