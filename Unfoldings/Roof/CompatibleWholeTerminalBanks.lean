module

public import Unfoldings.Roof.CompatibleTerminalCompletion
public import Unfoldings.Convex.ExteriorWholeBank
public import Unfoldings.Geometry.SpatialEnvelopeFaceSideCopies

/-! Construct whole original terminal banks in one retained cut model, including their endpoints. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting.WholeCutModel

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  {R : K.CompatiblePotentialRouting U G boundary a β}
  {M : G.FiniteSlopeModel} (W : R.WholeCutModel M)

local instance wholeTerminalIndexFintype : Fintype W.Index := W.finiteIndex

/-- Actual eventual support cells on the two original cut sides. Only geometric
cell and side data are retained; whole-bank metric properties are proved below. -/
structure TerminalSupportCells (r : {v // v ∈ R.parents.roots}) where
  anchor : Bool → W.Index
  sides : ∀ side, W.terminalSigns r (anchor side) = side
  threshold : ℝ
  tail : ∀ side t, threshold ≤ t →
    R.exterior.ray (R.terminalIndex r) t ∈ W.partition.footprint (anchor side)

/-- Select opposite actual eventual support cells from the whole finite partition. -/
def terminalSupportCells (r : {v // v ∈ R.parents.roots}) : W.TerminalSupportCells r :=
  Classical.choice (by
    obtain ⟨l, b, hl, hb, T, _, tail, _, _⟩ := W.terminal_roof_face_germs r
    refine ⟨⟨(fun side => if side then l else b), ?_, T, ?_⟩⟩
    · intro side
      cases side <;> assumption
    · intro side t after
      cases side
      · exact (tail t after).2
      · exact (tail t after).1)

namespace TerminalSupportCells

variable {W} {r : {v // v ∈ R.parents.roots}} (B : W.TerminalSupportCells r)

/-- The original side assignments are aligned with the actual exterior ray's equation. -/
theorem aligned_exterior : ∀ c x, x ∈ W.partition.footprint c →
    0 ≤ AffineArrangement.signed
      (orientMap (R.exterior.point (R.terminalIndex r))
        (R.exterior.ray (R.terminalIndex r) 1)) (W.terminalSigns r c) x := by
  intro c x member
  have bound := W.terminal_aligned r c x member
  rwa [R.terminal_exterior_equation r] at bound

/-- The original terminal cut is closed and lies on the actual exterior support line. -/
theorem cut_level : ∀ x ∈ R.terminalRayCut r,
    orientMap (R.exterior.point (R.terminalIndex r))
      (R.exterior.ray (R.terminalIndex r) 1) x = 0 := by
  rw [← R.terminal_exterior_equation r]
  exact MetricGluing.rayCut_on_line _ _

theorem cut_closed : IsClosed (R.terminalRayCut r) := MetricGluing.isClosed_rayCut _ _

/-- An entire closed one-sided bank in the actual original one-ray-cut model. -/
def oneRayBank (side : Bool) : ℝ≥0 → W.partition.Cut (R.terminalRayCut r) :=
  fun t => W.partition.faceSideRegionMap (B.anchor side)
    (orientMap (R.exterior.point (R.terminalIndex r)) (R.exterior.ray (R.terminalIndex r) 1))
    (orientMap_ne_zero (R.exterior.ray_endpoints_ne (R.terminalIndex r)))
    (W.terminalSigns r) (aligned_exterior (W := W)) (R.terminalRayCut r)
    (cut_closed (r := r)) (cut_level (r := r))
    (R.exterior.faceSideRaySource M W.partition (R.terminalIndex r) (B.anchor side)
      (W.terminalSigns r) B.threshold (B.tail side) t)

theorem restoreCut_oneRayBank (side : Bool) (t : ℝ≥0) :
    (W.partition.restoreCut (R.terminalRayCut r) (B.oneRayBank side t)).val =
      SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex r) t.val) := by
  exact (W.partition.restoreCut_faceSideRegionMap (B.anchor side)
    (orientMap (R.exterior.point (R.terminalIndex r)) (R.exterior.ray (R.terminalIndex r) 1))
    (orientMap_ne_zero (R.exterior.ray_endpoints_ne (R.terminalIndex r)))
    (W.terminalSigns r) (aligned_exterior (W := W)) (R.terminalRayCut r)
    (cut_closed (r := r)) (cut_level (r := r)) _).trans
      (SpatialEnvelope.point_eq_place M.plane (W.partition.support (B.anchor side))
        (R.exterior.terminal_cell_support_active M W.partition (R.terminalIndex r)
          (B.anchor side) B.threshold (B.tail side) t.val t.property)).symm

/-- The entire original bank has exactly the spatial exterior ray's metric. -/
theorem edist_oneRayBank (side : Bool) (s t : ℝ≥0) :
    edist (B.oneRayBank side s) (B.oneRayBank side t) =
      (‖R.exterior.spatialDirection (R.terminalIndex r)‖₊ : ℝ≥0∞) * edist s t := by
  let f := orientMap (R.exterior.point (R.terminalIndex r))
    (R.exterior.ray (R.terminalIndex r) 1)
  have proper : f ≠ 0 := orientMap_ne_zero (R.exterior.ray_endpoints_ne (R.terminalIndex r))
  let source := R.exterior.faceSideRaySource M W.partition (R.terminalIndex r) (B.anchor side)
    (W.terminalSigns r) B.threshold (B.tail side)
  have first := W.partition.faceSideRegionMap_isometry (B.anchor side) f proper
    (W.terminalSigns r) (aligned_exterior (W := W)) (R.terminalRayCut r)
    (cut_closed (r := r)) (cut_level (r := r))
  have last := W.partition.faceSideRegionMap_isometry (B.anchor side) f proper
    (W.terminalSigns r) (aligned_exterior (W := W))
    (MetricGluing.rayCut (R.exterior.point (R.terminalIndex r))
      (R.exterior.ray (R.terminalIndex r) 1)) (MetricGluing.isClosed_rayCut _ _)
    (MetricGluing.rayCut_on_line _ _)
  exact (first.edist_eq (source s) (source t)).trans
    ((last.edist_eq (source s) (source t)).symm.trans
      (R.exterior.edist_faceSideRayBank M W.partition (R.terminalIndex r) (B.anchor side)
        (W.terminalSigns r) (aligned_exterior (W := W)) B.threshold (B.tail side) s t))

/-- Each original one-ray-cut bank is a closed half-line dilation. -/
def oneRayBankDilation (side : Bool) : ℝ≥0 →ᵈ W.partition.Cut (R.terminalRayCut r) where
  toFun := B.oneRayBank side
  edist_eq' := ⟨‖R.exterior.spatialDirection (R.terminalIndex r)‖₊,
    nnnorm_ne_zero_iff.mpr (R.exterior.spatialDirection_ne_zero (R.terminalIndex r)),
    B.edist_oneRayBank side⟩

theorem horizontal_restoreCut_oneRayBank (side : Bool) (t : ℝ≥0) :
    Cap.horizontal (W.partition.restoreCut (R.terminalRayCut r) (B.oneRayBank side t)).val =
      R.exterior.ray (R.terminalIndex r) t.val :=
  (congrArg Cap.horizontal (B.restoreCut_oneRayBank side t)).trans
    (SpatialEnvelope.horizontal_point M.plane _)

theorem cut_line_forward : ∀ z ∈ rayForwardHalfspace
    (K.projectedVertex r.val) (R.wholeCutLast r.val),
    orientMap (R.exterior.point (R.terminalIndex r))
      (R.exterior.ray (R.terminalIndex r) 1) z = 0 → z ∈ R.terminalRayCut r := by
  intro z forward zero
  rw [← R.terminal_exterior_equation r] at zero
  obtain ⟨t, tpos, expression⟩ := exists_positive_ray_parameter
    (R.terminal_endpoints_ne r) forward zero
  exact ⟨⟨t, tpos.le⟩, expression.symm⟩

/-- Opposite entire banks retain distinct actual metric copies at every positive point. -/
theorem oneRayBank_ne (side other : Bool) (different : side ≠ other)
    (s t : ℝ≥0) (positive : 0 < s.val) : B.oneRayBank side s ≠ B.oneRayBank other t := by
  apply W.partition.faceSideRegionMap_ne_of_opposite_sign
    (orientMap (R.exterior.point (R.terminalIndex r)) (R.exterior.ray (R.terminalIndex r) 1))
    (orientMap_ne_zero (R.exterior.ray_endpoints_ne (R.terminalIndex r)))
    (W.terminalSigns r) (aligned_exterior (W := W)) (R.terminalRayCut r)
    (cut_closed (r := r)) (cut_level (r := r))
    (B.anchor side) (B.anchor other) _ _
    (isOpen_rayForwardHalfspace (K.projectedVertex r.val) (R.wholeCutLast r.val))
    (cut_line_forward (r := r))
  · change Cap.horizontal (W.partition.restoreCut (R.terminalRayCut r)
      (B.oneRayBank side s)).val ∈ _
    rw [B.horizontal_restoreCut_oneRayBank, ← R.terminal_lineMap r s.val]
    exact lineMap_mem_rayForwardHalfspace (R.terminal_endpoints_ne r) positive
  · simpa only [B.sides] using different

/-- Whole original rigid halfplane charts exist at every positive bank point. -/
theorem exists_oneRayBank_chart (side : Bool) (t : ℝ≥0) (positive : 0 < t.val) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ a : W.partition.faceSideHalfspace (B.anchor side)
        (orientMap (R.exterior.point (R.terminalIndex r))
          (R.exterior.ray (R.terminalIndex r) 1)) (W.terminalSigns r),
        a.val = (M.plane (W.partition.support (B.anchor side))).project.symm
          (R.exterior.ray (R.terminalIndex r) t.val) ∧
        ∃ C : Metric.eball (B.oneRayBank side t) (ENNReal.ofReal ε) ≃ᵢ Metric.ball a ε,
          ∀ y, (M.plane (W.partition.support (B.anchor side))).place (C y).val.val =
            (W.partition.restoreCut (R.terminalRayCut r) y.val).val := by
  let Q := M.plane (W.partition.support (B.anchor side))
  let source := R.exterior.faceSideRaySource M W.partition (R.terminalIndex r) (B.anchor side)
    (W.terminalSigns r) B.threshold (B.tail side) t
  have horizontal : Cap.horizontal (Q.place source.val) =
      R.exterior.ray (R.terminalIndex r) t.val :=
    (Q.horizontal_place _).trans (Q.project.apply_symm_apply _)
  obtain ⟨δ, δpos, face⟩ := R.exterior.terminal_cell_ray_germ M W.partition (R.terminalIndex r)
    (B.anchor side) B.threshold (B.tail side) (W.terminalSigns r (B.anchor side))
    (aligned_exterior (W := W) (B.anchor side)) positive
  apply W.partition.exists_faceSideHalfspace_ball_chart (B.anchor side)
    (orientMap (R.exterior.point (R.terminalIndex r)) (R.exterior.ray (R.terminalIndex r) 1))
    (orientMap_ne_zero (R.exterior.ray_endpoints_ne (R.terminalIndex r)))
    (W.terminalSigns r) (aligned_exterior (W := W)) (R.terminalRayCut r)
    (cut_closed (r := r)) (cut_level (r := r)) source
    (isOpen_rayForwardHalfspace (K.projectedVertex r.val) (R.wholeCutLast r.val))
    (cut_line_forward (r := r))
  · rw [horizontal, ← R.terminal_lineMap r t.val]
    exact lineMap_mem_rayForwardHalfspace (R.terminal_endpoints_ne r) positive
  · exact δpos
  · intro z near on_side
    exact face z (horizontal ▸ near) on_side

end TerminalSupportCells
end Unfoldings.ConvexRoof.CompatiblePotentialRouting.WholeCutModel

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  {M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel} (W : R.WholeCutModel M)

local instance constructedWholeTerminalIndexFintype : Fintype W.Index := W.finiteIndex

/-- Construct a whole original terminal bank in the full forest cut. Every parameter,
including zero, is retained, with no upper truncation and no metric certificate input. -/
def wholeTerminalBank (r : {v // v ∈ R.parents.roots}) (side : Bool) : ℝ≥0 →ᵈ W.Cut :=
  K.terminalClosedRayLiftDilation compact nonempty R no_boundary W r
    ((W.terminalSupportCells r).oneRayBankDilation side)
    ((W.terminalSupportCells r).horizontal_restoreCut_oneRayBank side)

/-- The constructed whole bank folds to the original roof ray at every parameter. -/
theorem restoreCut_wholeTerminalBank (r : {v // v ∈ R.parents.roots}) (side : Bool) (t : ℝ≥0) :
    (W.partition.restoreCut R.carrier
      (K.wholeTerminalBank compact nonempty R no_boundary W r side t)).val =
        SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex r) t.val) := by
  let B := W.terminalSupportCells r
  exact (congrArg PolygonalPoint.val
    (K.restoreCut_terminalClosedRayLift compact nonempty R no_boundary W r
      (B.oneRayBankDilation side) (B.horizontal_restoreCut_oneRayBank side)
      (Dilation.lipschitzWith (B.oneRayBankDilation side)) t)).trans
        (B.restoreCut_oneRayBank side t)

/-- Exact full spatial speed for each pair of points on the entire original closed bank. -/
theorem edist_wholeTerminalBank (r : {v // v ∈ R.parents.roots}) (side : Bool) (s t : ℝ≥0) :
    edist (K.wholeTerminalBank compact nonempty R no_boundary W r side s)
      (K.wholeTerminalBank compact nonempty R no_boundary W r side t) =
        (‖R.exterior.spatialDirection (R.terminalIndex r)‖₊ : ℝ≥0∞) * edist s t := by
  let B := W.terminalSupportCells r
  exact (K.edist_terminalClosedRayLift compact nonempty R no_boundary W r
    (B.oneRayBankDilation side) (B.horizontal_restoreCut_oneRayBank side) s t).trans
      (B.edist_oneRayBank side s t)

theorem wholeTerminalBank_isClosedEmbedding (r : {v // v ∈ R.parents.roots}) (side : Bool) :
    Topology.IsClosedEmbedding (K.wholeTerminalBank compact nonempty R no_boundary W r side) :=
  Dilation.isClosedEmbedding (K.wholeTerminalBank compact nonempty R no_boundary W r side)

/-- Opposite constructed full-forest banks cannot meet at a positive ray parameter.
Their completed endpoints retain whatever original cut copies the forest determines. -/
theorem wholeTerminalBank_ne (r : {v // v ∈ R.parents.roots}) (side other : Bool)
    (different : side ≠ other) (s t : ℝ≥0) (positive : 0 < s.val) :
    K.wholeTerminalBank compact nonempty R no_boundary W r side s ≠
      K.wholeTerminalBank compact nonempty R no_boundary W r other t := by
  let B := W.terminalSupportCells r
  intro equal
  apply B.oneRayBank_ne side other different s t positive
  exact (K.forgetCut_terminalClosedRayLift compact nonempty R no_boundary W r
    (B.oneRayBankDilation side) (B.horizontal_restoreCut_oneRayBank side)
    (Dilation.lipschitzWith (B.oneRayBankDilation side)) s).symm.trans
      ((congrArg (W.partition.forgetCut R.carrier (R.terminalRayCut r)
        (R.terminalRayCut_subset_carrier r)) equal).trans
          (K.forgetCut_terminalClosedRayLift compact nonempty R no_boundary W r
            (B.oneRayBankDilation other) (B.horizontal_restoreCut_oneRayBank other)
            (Dilation.lipschitzWith (B.oneRayBankDilation other)) t))

end Unfoldings.ConvexRoof
