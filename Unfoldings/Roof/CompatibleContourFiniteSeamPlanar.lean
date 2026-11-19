module

public import Unfoldings.Roof.CompatibleContourFiniteBankCharts
public import Unfoldings.Roof.CompatibleContourFiniteSeamBalls
public import Unfoldings.Metric.FiniteBankHalfPlaneGluing
public import Unfoldings.Metric.LocalBallRegularity

/-! Every ordinary finite seam of the actual canonical graft is locally planar. -/

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

local instance contourFiniteSeamPlanarMeshFintype : Fintype (T).Index :=
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

local instance contourFiniteSeamPlanarWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Models" => fun event => OrientedBankGap.model (geometry event)

local notation "Pieces" => K.compatibleContourGraftPiece compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour starts W Models
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Base" => K.compatibleContourBaseMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W Models
local notation "Gap" => K.compatibleContourGapMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W Models

local notation "Vertex" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "SlotAt[" v "," i "]" => (Sigma.mk (Sum.inl v) i : BankStackSlot Stack)

local notation "LeftAt" => bankStackLeft Pieces Stack Base Gap
local notation "RightAt" => bankStackRight Pieces Stack Base Gap
local notation "Banks" => bankSeams LeftAt RightAt

/-- A point in the strict interior of any original finite attachment has a whole
planar metric ball in the canonical full graft. This includes an empty gap stack. -/
theorem compatibleContourFiniteSeam_planarBall
    (vertex : Vertex) (i : Fin ((Stack (.inl vertex)).length + 1)) (t : unitInterval)
    (bounds : 0 < t ∧ t < 1) :
    HasMetricBallChart ℂ (point Pieces Banks (LeftAt SlotAt[vertex,i] t)) := by
  let slot := SlotAt[vertex,i]
  let left := bankStackLeftCurve Stack Pieces Base Gap slot
  let right := bankStackRightCurve Stack Pieces Base Gap slot
  let pair := bankPairGlue Pieces left right
  let single := bankSeams (fun (_ : Unit) (s : unitInterval) => LeftAt slot s)
    (fun (_ : Unit) (s : unitInterval) => RightAt slot s)
  let x := point Pieces pair ⟨_, left t⟩
  have left_label (s : unitInterval) := bankStackLeft_curve Stack Pieces Base Gap slot s
  have right_label (s : unitInterval) := bankStackRight_curve Stack Pieces Base Gap slot s
  obtain ⟨⟨speed, speed_pos, lm, r₁, ⟨L⟩⟩, ⟨b, bpos, rm, r₂, ⟨B⟩⟩⟩ :=
    K.compatibleContourFiniteSlot_charts compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W geometry vertex i t bounds
  let bm := K.compatibleContourBaseMark_metric compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W Models
  let gm := K.compatibleContourGapMark_metric compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W Models
  have one : edist (0 : unitInterval) 1 = 1 := by
    rw [edist_dist]
    change ENNReal.ofReal (dist (0 : ℝ) 1) = 1
    norm_num [Real.dist_eq]
  have equal_speed : speed = b := by
    have same := bankStackCurves_same_metric Stack Pieces Base Gap bm gm slot 0 1
    have lengths := (lm 0 1).symm.trans (same.trans (rm 0 1))
    rw [one, mul_one, mul_one] at lengths
    exact (ENNReal.ofReal_eq_ofReal_iff speed_pos.le bpos.le).mp lengths
  subst b
  have arclength (s : unitInterval) :
      ENNReal.ofReal speed * edist t s = ENNReal.ofReal (|(s : ℝ) - t| * speed) := by
    rw [edist_dist, ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
    change ENNReal.ofReal (dist t.val s.val) * _ = _
    rw [Real.dist_eq, abs_sub_comm]
  have base_closed := K.compatibleContourBaseMark_isClosedEmbedding compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W Models
  have gap_closed := K.compatibleContourGapMark_isClosedEmbedding compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W Models
  have unique := K.compatibleContourFiniteMarks_unique compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W Models geometry vertex t bounds
  have nodup := K.compatibleContourBankStack_nodup compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour
  have wrong_left (s : unitInterval) : (⟨_, right t⟩ : Total Pieces) ≠ ⟨_, left s⟩ := by
    intro eq
    have equal : LeftAt slot s = RightAt slot t :=
      (left_label s).trans (eq.symm.trans (right_label t).symm)
    have sides := bankStackEndpoint_eq_of_unique Stack Pieces Base Gap nodup slot t unique
      true false slot s equal
    cases congrArg Prod.fst sides
  have wrong_right (s : unitInterval) : (⟨_, left t⟩ : Total Pieces) ≠ ⟨_, right s⟩ := by
    intro eq
    have equal : RightAt slot s = LeftAt slot t :=
      (right_label s).trans (eq.symm.trans (left_label t).symm)
    have sides := bankStackEndpoint_eq_of_unique Stack Pieces Base Gap nodup slot t unique
      false true slot s equal
    cases congrArg Prod.fst sides
  have planar : HasMetricBallChart ℂ x :=
    finiteBankPair_planarBall_of_charts Pieces left right t L B speed_pos bounds
      (fun s => (lm t s).trans (arclength s)) (fun s => (rm t s).trans (arclength s))
      (bankStackLeftCurve_closed Stack Pieces Base Gap base_closed gap_closed slot).isClosed_range
      (bankStackRightCurve_closed Stack Pieces Base Gap base_closed gap_closed slot).isClosed_range
      wrong_left wrong_right
  have seams (p q : Total Pieces) : pair p q ↔ single p q := by
    constructor
    · rintro ⟨s, hp, hq⟩
      exact ⟨(), s, hp.trans (left_label s).symm, hq.trans (right_label s).symm⟩
    · rintro ⟨_, s, hp, hq⟩
      exact ⟨s, hp.trans (left_label s), hq.trans (right_label s)⟩
  let E := changeSeamsIsometryEquiv Pieces (R := pair) (S := single)
    (fun p q h => point_eq_of_glue Pieces ((seams p q).mp h))
    (fun p q h => point_eq_of_glue Pieces ((seams p q).mpr h))
  have center : E x = point Pieces single (LeftAt slot t) :=
    congrArg (point Pieces single) (left_label t).symm
  obtain ⟨r, rpos, A, based⟩ := K.compatibleContourFiniteSeam_singleSlot_ball compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W Models geometry
      vertex i t bounds
  have core : HasMetricBallChart ℂ (point Pieces single (LeftAt slot t)) := by
    rw [← center]
    exact planar.isometryEquiv E
  exact core.of_centered_ball_equiv rpos A based

end Unfoldings.ConvexRoof
