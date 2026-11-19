module

public import Unfoldings.Roof.CompatibleContourFiniteSeamPlanar
public import Unfoldings.Roof.CompatibleContourTerminalBankCharts

/-! Every positive terminal seam of the actual canonical graft is locally planar. -/

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

local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance contourTerminalSeamPlanarMeshFintype : Fintype (T).Index :=
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
      (K.compatibleContourOpenedBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance contourTerminalSeamPlanarWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Models" => fun event => OrientedBankGap.model (geometry event)

local notation "Pieces" => K.compatibleContourGraftPiece compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour starts W Models
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Base" => K.compatibleContourBaseMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W Models
local notation "Gap" => K.compatibleContourGapMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W Models

local notation "Edge" => TriangleComplex.ContourTerminalEdge D Selection
local notation "SlotAt[" e "," i "]" => (Sigma.mk (Sum.inr e) i : BankStackSlot Stack)

local notation "LeftAt" => bankStackLeft Pieces Stack Base Gap
local notation "RightAt" => bankStackRight Pieces Stack Base Gap
local notation "Banks" => bankSeams LeftAt RightAt

/-- A point in the strict interior of any original terminal attachment has a whole
planar metric ball in the canonical full graft. This includes an empty gap stack. -/
theorem compatibleContourTerminalSeam_planarBall
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (t : ℝ≥0)
    (positive_time : 0 < t) :
    HasMetricBallChart ℂ (point Pieces Banks (LeftAt SlotAt[edge,i] t)) := by
  let slot := SlotAt[edge,i]
  obtain ⟨⟨speed, speed_pos, lm, r₁, ⟨L⟩⟩, ⟨b, bpos, rm, r₂, ⟨B⟩⟩⟩ :=
    K.compatibleContourTerminalSlot_charts compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W geometry edge i t positive_time
  let bm := K.compatibleContourBaseMark_metric compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W Models
  let gm := K.compatibleContourGapMark_metric compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W Models
  have one : edist (0 : ℝ≥0) 1 = 1 := by
    rw [edist_dist]
    change ENNReal.ofReal (dist (0 : ℝ) 1) = 1
    norm_num [Real.dist_eq]
  have equal_speed : speed = b := by
    have same := bankStackCurves_same_metric Stack Pieces Base Gap bm gm slot 0 1
    have lengths := (lm 0 1).symm.trans (same.trans (rm 0 1))
    rw [one, mul_one, mul_one] at lengths
    exact (ENNReal.ofReal_eq_ofReal_iff speed_pos.le bpos.le).mp lengths
  subst b
  have arclength (s : ℝ≥0) :
      ENNReal.ofReal speed * edist t s = ENNReal.ofReal (|(s : ℝ) - t| * speed) := by
    rw [edist_dist, ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
    change ENNReal.ofReal (dist t.val s.val) * _ = _
    change ENNReal.ofReal |t.val - s.val| * ENNReal.ofReal speed =
      ENNReal.ofReal |s.val - t.val| * ENNReal.ofReal speed
    rw [abs_sub_comm]
  have unique := K.compatibleContourTerminalMarks_unique compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W Models geometry edge t positive_time
  have interior_time : t.val ∈ interior (Set.range (Subtype.val : ℝ≥0 → ℝ)) := by
    have range_eq : Set.range (Subtype.val : ℝ≥0 → ℝ) = Set.Ici 0 := by
      ext x
      exact ⟨fun ⟨s, eq⟩ => eq ▸ s.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
    have room : interior (Set.Ici (0 : ℝ)) = Set.Ioi 0 := interior_Ici
    have time : t.val ∈ Set.Ioi (0 : ℝ) := positive_time
    exact (congrArg interior range_eq).symm ▸ (room.symm ▸ time)
  exact K.compatibleContourBankSlot_planarBall compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W geometry slot t Subtype.val L B speed_pos
    interior_time (fun s => (lm t s).trans (arclength s))
    (fun s => (rm t s).trans (arclength s)) unique

end Unfoldings.ConvexRoof
