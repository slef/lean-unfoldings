module

public import Unfoldings.FewestNets.AcuteLatitudeAnnularRouting
public import Unfoldings.FewestNets.ThreeExitSharpSourceGaps
public import Unfoldings.Roof.AffineFloorSelectorCurvature
public import Unfoldings.Cap.SharpSectionFans

/-! The revised annular selector leaves a genuine gap at every actual source. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting

open FewestNets Real MeasureTheory
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

local instance acuteLatitudeSourceIndexFintype (level : ℝ) (higher : ∀ v : V, (G).height (p v) < level) :
    Fintype (T[level,higher]).Index := @Fintype.ofFinite _ (T[level,higher]).finite

set_option maxHeartbeats 2400000 in
/-- The revised annular cells have a complete contour of genuine opened gaps.
The count and the gap construction use the same actual normal selector. -/
theorem exists_acuteLatitude_sourceContour {a : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6)
    (volume_bound : volume slopes < ENNReal.ofReal (0.0163 * a))
    (radius : ∀ q ∈ slopes, ‖q‖ ≤ tan (0.568 * AcuteLatitudeGrid.radius a))
    (span : ∀ r : Root, let exit := (R.rootHeadingChart r (R.rootExitDirection r)).arg
      let lo := R.rootWindowStart r
      max (lo + H.width) exit - min lo exit ≤ π / 2 - 0.170 * a) :
    ∃ (level : ℝ) (S : FloorWindowModel.SourceContour (R := R) (M := M) (level := level)),
      (D[level,S.higher]).contourOriginalVertex Sel[level,S.higher] S.contour
        (Fin.last S.contour.length) ∈ (F[level,S.higher]).parents.roots ∧
      (∀ v : (D[level,S.higher]).Vertex Set.univ,
        0 < (D[level,S.higher]).interiorAngularDefect Set.univ v →
        ∃ e : (D[level,S.higher]).PositiveContourSource Sel[level,S.higher] S.contour,
          (D[level,S.higher]).positiveContourVertex Sel[level,S.higher] S.contour e = v) ∧
      ∀ (e : (D[level,S.higher]).PositiveContourSource Sel[level,S.higher] S.contour)
        (k : Fin ((D[level,S.higher]).positiveContourBankLength Sel[level,S.higher] S.contour e)),
        let bank := (F[level,S.higher]).contourSourceRay S.contour S.starts e
        0 < inner ℝ (bank.chain.vertex k.succ.castSucc - bank.start) (bank.chain.edge k.succ) := by
  obtain ⟨level, higher⟩ := exists_truncation_level
    (K := K) (slopes := slopes) (seed := seed) (B := B) (compact := compact) (nonempty := nonempty)
  obtain ⟨contour, starts, ends, coverage⟩ := R.exists_fineMesh_completeSourceContour level M higher
  let T := T[level,higher]
  let inside := meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M higher
  let φ := 0.568 * AcuteLatitudeGrid.radius a
  let Ω := (volume slopes).toReal
  have Ω_nonneg : 0 ≤ Ω := ENNReal.toReal_nonneg
  have Ω_bound : Ω < 0.0163 * a := by
    exact (ENNReal.toReal_lt_toReal (volume_bound.trans ENNReal.ofReal_lt_top).ne ENNReal.ofReal_ne_top).mpr
      volume_bound |>.trans_eq (ENNReal.toReal_ofReal (by positivity))
  have φ_pos : 0 < φ := mul_pos (by norm_num) (AcuteLatitudeGrid.radius_pos positive)
  obtain ⟨φ_small, φ_square, cosine, _⟩ :=
    acute_latitude_tilt_budgets positive small φ_pos.le (le_refl φ)
  have φ_acute : φ < π / 2 := by linarith only [φ_small, pi_gt_three]
  have tilt (i : M.Face) : cos φ ≤ (M.plane i).normal 2 :=
    SpatialPlane.ofGraph_normal_height_of_slope_radius φ_pos φ_acute _ _
      (radius _ (M.included i.val i.property))
  have curvature {J : Type} {extra : J → Plane →ᵃ[ℝ] ℝ}
      (A : SpatialEnvelope.FloorMesh M.plane (SlopeEnvelope.FiniteSlopeModel.referenceFloor B.reference)
        extra (-level)) :
      letI : Fintype A.Index := @Fintype.ofFinite _ A.finite
      A.pairedComplex.totalInteriorAngularDefect Set.univ ≤ Ω := by
    let : Fintype A.Index := @Fintype.ofFinite _ A.finite
    have h := M.floorRoof_curvature_le_selector_volume A inside B.convex
    have nonnegative := (A.roof inside).totalCurvature_nonneg
    have real_bound := ENNReal.toReal_mono (volume_bound.trans ENNReal.ofReal_lt_top).ne h
    rw [ENNReal.toReal_ofReal nonnegative] at real_bound
    exact real_bound
  have acute := acute_latitude_closing_budget positive φ_pos.le φ_small.le φ_square Ω_bound
  rw [ConvexCap.cos_ratio_eq_tan_half_sq cosine] at acute
  have fit : π / 2 - 0.170 * a +
      (2 * (2 * arcsin (tan (φ / 2) ^ 2)) + 2 * φ * sin φ + Ω) + Ω < π / 2 := by
    linarith only [acute, Ω_nonneg]
  have total_small : (D[level,higher]).totalInteriorAngularDefect Set.univ < π :=
    (curvature T).trans_lt (by linarith only [Ω_bound, small, pi_pos])
  have gap (e : (D[level,higher]).PositiveContourSource Sel[level,higher] contour) :
      OrientedBankGap ((F[level,higher]).contourSourceRay contour starts e)
        ((F[level,higher]).contourSourceOpenedRay contour starts e) ∧
      ∀ k : Fin ((D[level,higher]).positiveContourBankLength Sel[level,higher] contour e),
        let bank := (F[level,higher]).contourSourceRay contour starts e
        0 < inner ℝ (bank.chain.vertex k.succ.castSucc - bank.start) (bank.chain.edge k.succ) := by
    obtain ⟨center, prior, _⟩ := R.contourSource_common_acuteCone M level higher contour starts e
      φ_pos.le φ_acute Ω_nonneg tilt (fun L => curvature L.mesh) (curvature T) span fit
    exact (F[level,higher]).contourSource_gap_of_acuteCone contour starts e total_small prior
  exact ⟨level, ⟨higher, contour, starts, fun e => (gap e).1⟩, ends, coverage, fun e => (gap e).2⟩

end Unfoldings.ConvexRoof.ThreeExitComponentRouting
