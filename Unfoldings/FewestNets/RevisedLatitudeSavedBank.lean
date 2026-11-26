module

public import Unfoldings.FewestNets.ThreeExitSavedBankCone
public import Unfoldings.Roof.SignedBankWindows
public import Unfoldings.Roof.AffineFloorSelectorCurvature
public import Unfoldings.Geometry.GraphNormalTilt

/-! The signed cell allowance controls all histories of an actual revised routed component. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting

open FewestNets Real MeasureTheory Cap
open scoped ENNReal

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : ThreeExitStemWindows}
  (R : K.ThreeExitComponentRouting seed B compact nonempty H)

local notation "U" => K.selectionComponent slopes seed
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ K.restrictedCarrier U}
local notation "G₀" => K.componentClippedExtension
  (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty
local notation "G" => SlopeEnvelope.recenter (G₀) B.reference
local notation "p" => (fun v : V => K.projectedVertex (Subtype.val v))
local notation "Root" => {r : V // r ∈ R.stems.choice.parents.roots}

variable (M : (K.componentClippedExtension
  (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty).FiniteSlopeModel)

local notation "T[" level "," higher "]" => R.fineMesh level M higher
local notation "D[" level "," higher "]" => SpatialEnvelope.FloorMesh.pairedComplex (T[level,higher])
local notation "F[" level "," higher "]" => R.fineMeshForest level M higher
local notation "Sel[" level "," higher "]" => PotentialCutForest.selection (F[level,higher])

local instance signedSourceIndexFintype (level : ℝ) (higher : ∀ v : V, (G).height (p v) < level) :
    Fintype (T[level,higher]).Index := @Fintype.ofFinite _ (T[level,higher]).finite

local notation "Q[" level "," higher "]" => SpatialEnvelope.FloorMesh.roof T[level,higher]
  (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M higher)

set_option maxHeartbeats 2500000 in
/-- Compare every actual saved-bank window with its projected history using the
signed allowance of the same normal cell used for routing. -/
theorem savedHeadingBound_signed {φ D : ℝ} (φpos : 0 < φ) (φsmall : φ < π / 2)
    (radius : ∀ x ∈ slopes, ‖x‖ ≤ tan φ) (Dn : 0 ≤ D)
    (area : ∀ x ∈ slopes, ∀ y ∈ slopes, |orient 0 x y| / 2 ≤ D) :
    R.SavedHeadingBound M (2 * arcsin ((1 - cos φ) / (1 + cos φ)) +
      (solidAngleMeasure (gnomonicNormal '' slopes)).toReal + D) := by
  intro level higher contour starts event
  let bank := (F[level,higher]).contourSourceBankChain contour starts event
  let source := (D[level,higher]).positiveContourVertex (Sel[level,higher]) contour event
  let n := (D[level,higher]).positiveContourBankLength (Sel[level,higher]) contour event
  dsimp only
  intro axis unit forward acute i j
  have internal (k : Fin n) :
      (Q[level,higher]).projectedVertex ((D[level,higher]).vertexForgetCuts (Set.subset_univ _)
        ((D[level,higher]).boundaryEndVertex _ (bank.point k.succ))) ∈ interior (Q[level,higher]).footprint := by
    apply ((Q[level,higher]).projectedVertex_mem_interior_iff _).mpr
    intro boundary
    have root := (F[level,higher]).boundary_roots boundary
    rw [(F[level,higher]).contourSourceBankChain_original contour starts event k.succ] at root
    exact (F[level,higher]).parents.iterate_lt_distanceToRoot_not_mem source
      (by rw [(D[level,higher]).positiveContourBank_span (Sel[level,higher]) contour event]; exact k.succ.isLt) root
  have present (q : M.Face) : (M.plane q).normalSlope ∈ slopes := by
    rw [M.normalSlope]
    exact M.included _ q.property
  have tilt (q : M.Face) : cos φ ≤ (M.plane q).normal 2 :=
    SpatialPlane.ofGraph_normal_height_of_slope_radius φpos φsmall _ _
      (radius _ (M.included q.val q.property))
  have ordered (i j : Fin (n + 1)) (before : i ≤ j) :
      |(Q[level,higher]).projectedMetricHeadingError bank i -
        (Q[level,higher]).projectedMetricHeadingError bank j| ≤
          2 * arcsin ((1 - cos φ) / (1 + cos φ)) +
            (solidAngleMeasure (gnomonicNormal '' slopes)).toReal + D :=
    (T[level,higher]).abs_projectedMetricHeadingError_sub_le_signed_of_direction
      (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M higher)
      bank axis unit forward acute ((F[level,higher]).contourSourceBankChain_cut contour starts event)
      internal compact B.convex present φpos.le φsmall Dn tilt area i j before
  rcases le_total i j with before | after
  · exact ordered i j before
  · rw [abs_sub_comm]
    exact ordered j i after

include M in
set_option maxHeartbeats 2400000 in
/-- The actual original-edge component is a net under the revised angular
and solid-angle allowance, including the one pole-triangle area. -/
theorem hasOriginalEdgeNet_of_signed_cellAllowance {φ D σ : ℝ}
    (selected : K.normalSlope seed ∈ slopes)
    (φpos : 0 < φ) (φsmall : φ < π / 4)
    (radius : ∀ x ∈ slopes, ‖x‖ ≤ tan φ)
    (area : ∀ x ∈ slopes, ∀ y ∈ slopes, |orient 0 x y| / 2 ≤ D)
    (reserve : 2 * arcsin ((1 - cos φ) / (1 + cos φ)) +
      (solidAngleMeasure (gnomonicNormal '' slopes)).toReal + D < σ)
    (span : ∀ r : Root, let exit := (R.rootHeadingChart r (R.rootExitDirection r)).arg
      let lo := R.rootWindowStart r
      max (lo + H.width) exit - min lo exit ≤ π / 2 - σ) :
    C.HasOriginalEdgeNet U := by
  have small : φ < π / 2 := φsmall.trans (by linarith only [pi_pos])
  let q := nonempty.some
  have hq : q ∈ slopes := nonempty.some_mem
  have Dn : 0 ≤ D := (by positivity : 0 ≤ |orient 0 q q| / 2).trans (area q hq q hq)
  have cp : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith only [pi_pos, φpos], small⟩
  have delta : 0 ≤ arcsin ((1 - cos φ) / (1 + cos φ)) :=
    arcsin_nonneg.mpr (div_nonneg (sub_nonneg.mpr (cos_le_one _)) (by positivity))
  have error_nonneg : 0 ≤ 2 * arcsin ((1 - cos φ) / (1 + cos φ)) +
      (solidAngleMeasure (gnomonicNormal '' slopes)).toReal + D := by positivity
  have tan_pos := Real.tan_pos_of_pos_of_lt_pi_div_two φpos small
  have tan_small : tan φ < 1 := by
    rw [← Real.tan_pi_div_four]
    exact Real.strictMonoOn_tan (show φ ∈ Set.Ioo (-(π / 2)) (π / 2) from
      ⟨by linarith only [φpos, pi_pos], small⟩)
      (show π / 4 ∈ Set.Ioo (-(π / 2)) (π / 2) from
        ⟨by linarith only [pi_pos], by linarith only [pi_pos]⟩) φsmall
  have vol : volume slopes < ENNReal.ofReal π := by
    apply (measure_mono (show slopes ⊆ Metric.closedBall (0 : Plane) (tan φ) from fun x hx => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact radius x hx)).trans_lt
    rw [EuclideanSpace.volume_closedBall_fin_two, ← ENNReal.ofReal_pow tan_pos.le,
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    apply (ENNReal.ofReal_lt_ofReal_iff pi_pos).mpr
    have sq : tan φ ^ 2 < (1 : ℝ) ^ 2 := (sq_lt_sq₀ tan_pos.le zero_le_one).mpr tan_small
    rw [one_pow] at sq
    have h : tan φ ^ 2 * π < (1 : ℝ) * π := mul_lt_mul_of_pos_right sq pi_pos
    simpa only [one_mul] using h
  have curvature (level : ℝ) (higher : ∀ v : V, (G).height (p v) < level) :
      (D[level,higher]).totalInteriorAngularDefect Set.univ < π := by
    have estimate := M.floorRoof_curvature_le_selector_volume (T[level,higher])
      (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M higher) B.convex
    exact (ENNReal.ofReal_lt_ofReal_iff pi_pos).mp (estimate.trans_lt vol)
  exact R.hasOriginalEdgeNet_of_savedHeadingBound M selected error_nonneg span
    (R.savedHeadingBound_signed M φpos small radius Dn area) (by linarith only [reserve]) curvature

end Unfoldings.ConvexRoof.ThreeExitComponentRouting
