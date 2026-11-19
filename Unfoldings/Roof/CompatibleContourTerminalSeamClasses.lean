module

public import Unfoldings.Roof.CompatibleContourGraftExactness
public import Unfoldings.Roof.CompatibleContourTerminalSideLabels

/-! Every positive original terminal seam has an exact two-mark class. -/

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

local instance contourTerminalSeamMeshFintype : Fintype (T).Index :=
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

local instance contourTerminalSeamWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Pieces" => K.compatibleContourGraftPiece compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour starts W models
local notation "Base" => K.compatibleContourBaseMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Gap" => K.compatibleContourGapMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models

local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute

local notation "Edge" => TriangleComplex.ContourTerminalEdge D Selection

/-- At a positive terminal time, a roof mark uniquely names its original tail and side
among all actual original finite and terminal marks. -/
theorem compatibleContourBaseMark_eq_terminal_positive
    (edge : Edge) (other : Attachment) (side other_side : Bool)
    (t : ℝ≥0) (s : ParamAt other) (positive_time : 0 < t)
    (equal : Base other other_side s = Base (.inr edge) side t) :
    other_side = side ∧ (⟨other, s⟩ : Σ b, ParamAt b) = ⟨.inr edge, t⟩ := by
  cases other with
  | inl vertex =>
    exact (K.compatibleContourParentMark_ne_terminal_positive compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W vertex.val vertex.property
        other_side s edge side t positive_time equal).elim
  | inr other =>
    have labels := K.compatibleContourTerminalMark_eq compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W edge other side other_side t s equal
    have edges := congrArg Prod.fst labels
    have flags := congrArg (fun x => x.2.1) labels
    have times := congrArg (fun x => x.2.2) labels
    dsimp only at edges flags times
    subst other
    subst s
    exact ⟨flags, rfl⟩

/-- The actual paired roof and gap tail marks are unique at every strictly positive time. -/
theorem compatibleContourTerminalMarks_unique
    (geometry : ∀ event : (D).PositiveContourSource Selection contour,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (edge : Edge) (t : ℝ≥0) (positive_time : 0 < t) :
    MetricGluing.BankStackUniqueMarksAt Stack Pieces Base Gap (.inr edge) t := by
  constructor
  · intro side other other_side s equal
    exact K.compatibleContourBaseMark_eq_terminal_positive compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W models edge other side other_side
        t s positive_time equal
  · intro event member side other other_member other_side s equal
    exact K.compatibleContourGapMark_eq_interior compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models event (geometry event) (.inr edge)
      other member other_member side other_side t s positive_time equal

local notation "LeftAt" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "RightAt" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams LeftAt RightAt

/-- The original metric class has exactly its two consecutive bank representatives. -/
theorem compatibleContourTerminalSeam_point_eq_iff
    (geometry : ∀ event : (D).PositiveContourSource Selection contour,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1))
    (t : ℝ≥0) (positive_time : 0 < t) (x : MetricGluing.Total Pieces) :
    MetricGluing.point Pieces Banks (LeftAt ⟨.inr edge, i⟩ t) =
      MetricGluing.point Pieces Banks x ↔
      x = LeftAt ⟨.inr edge, i⟩ t ∨ x = RightAt ⟨.inr edge, i⟩ t := by
  apply (K.compatibleContourGraft_point_eq_iff compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W models geometry _ x).trans
  exact MetricGluing.bankStack_eqvGen_pair_iff Stack Pieces Base Gap
    (K.compatibleContourBankStack_nodup compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour) ⟨.inr edge, i⟩ t
    (K.compatibleContourTerminalMarks_unique compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models geometry edge t positive_time) x

end Unfoldings.ConvexRoof
