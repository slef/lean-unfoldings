module

public import Unfoldings.Roof.CompatibleContourSingleSlotGraft
public import Unfoldings.Metric.ForgetChartTransport

/-! Actual ordinary finite graft balls equal centered balls of the original single-bank graft. -/

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

local notation "inside" => K.compatible_section_interior compact nonempty R level higher M

local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance contourFiniteBallMeshFintype : Fintype (T).Index :=
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

local instance contourFiniteBallWholeFintype : Fintype W.Index := W.finiteIndex

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
local notation "KeepAt[" slot "]" => K.compatibleContourKeepBankSlot compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models slot
local notation "ReducedAt[" slot "]" => MetricGluing.ClosedSeams.restrict Seams KeepAt[slot]
local notation "SlotLeft[" slot "]" => fun (_ : Unit)
    (t : ParamAt[Sigma.fst (slot : MetricGluing.BankStackSlot Stack)]) =>
  MetricGluing.bankStackLeft Pieces Stack Base Gap slot t
local notation "SlotRight[" slot "]" => fun (_ : Unit)
    (t : ParamAt[Sigma.fst (slot : MetricGluing.BankStackSlot Stack)]) =>
  MetricGluing.bankStackRight Pieces Stack Base Gap slot t
local notation "SlotGlue[" slot "]" => MetricGluing.mappedBankGraftCells Cells Inner Coordinates
  SlotLeft[slot] SlotRight[slot]

local notation "SlotPoint[" slot "]" => MetricGluing.point Pieces
  (MetricGluing.bankSeams SlotLeft[slot] SlotRight[slot])
local notation "LeftAt[" slot "," t "]" => MetricGluing.bankStackLeft Pieces Stack Base Gap slot t

/-- Every ordinary finite graft point has a whole centered ball identical to the graft
along just its original bank pair. No original-cell representative, local chart or
nonoverlap premise is required. Empty stacks and two banks of the same roof are included. -/
theorem compatibleContourFiniteSeam_singleSlot_ball
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (vertex : {v : (D).Vertex Set.univ // v ∉ (Fcut).parents.roots})
    (i : Fin ((Stack (.inl vertex)).length + 1)) (t : unitInterval) (bounds : 0 < t ∧ t < 1) :
    ∃ (r : ℝ) (positive_radius : 0 < r),
      ∃ A : ↥(Metric.eball
          (SlotPoint[⟨.inl vertex,i⟩] LeftAt[⟨.inl vertex,i⟩,t]) (ENNReal.ofReal r)) ≃ᵢ
        ↥(Metric.eball (MetricGluing.point Pieces Banks LeftAt[⟨.inl vertex,i⟩,t])
          (ENNReal.ofReal r)),
        (A ⟨SlotPoint[⟨.inl vertex,i⟩] LeftAt[⟨.inl vertex,i⟩,t],
          Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive_radius)⟩).val =
            MetricGluing.point Pieces Banks LeftAt[⟨.inl vertex,i⟩,t] := by
  let slot : MetricGluing.BankStackSlot Stack := ⟨.inl vertex, i⟩
  obtain ⟨a, center⟩ := MetricGluing.mappedNestedPoint_surjective Cells Inner Coordinates
    LeftAt[slot,t]
  obtain ⟨C⟩ := K.compatibleContourFiniteSeam_forgetChart compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W models geometry vertex i t bounds
      a center
  let first := K.compatibleContourSingleSlotIsometry compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W models slot
  let last := K.compatibleContourClosedSeamIsometry compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W models
  have first_center : first (MetricGluing.point Raw (ReducedAt[slot]).relation a) =
      SlotPoint[slot] LeftAt[slot,t] :=
    (K.compatibleContourSingleSlotIsometry_point compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models slot a).trans
      (congrArg SlotPoint[slot] center)
  have last_center : last (MetricGluing.point Raw (Seams).relation a) =
      MetricGluing.point Pieces Banks LeftAt[slot,t] := by
    have original : last (MetricGluing.point Raw (Seams).relation a) =
        MetricGluing.point Pieces Banks (Original a) := rfl
    exact original.trans (congrArg (MetricGluing.point Pieces Banks) center)
  exact ⟨C.radius, C.positive,
    C.transportBall first last _ _ first_center last_center,
    C.transportBall_center first last _ _ first_center last_center⟩

end Unfoldings.ConvexRoof
