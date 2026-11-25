module

public import Unfoldings.FewestNets.LatitudeTriangleRouting
public import Unfoldings.FewestNets.ThreeExitSourceGaps

/-! The latitude tilt leaves a genuine source-only gap at every event of the exact contour. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting

open FewestNets Real

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

local instance latitudeSourceIndexFintype (level : ℝ) (higher : ∀ v : V, (G).height (p v) < level) :
    Fintype (T[level,higher]).Index := @Fintype.ofFinite _ (T[level,higher]).finite

set_option maxHeartbeats 1900000 in
-- The fine roof, its actual contour, and all original ray banks use the same extension.
/-- At the latitude scales the constructed contour processes all positive
curvature, and every positive source has a genuine oriented Jordan gap. -/
theorem exists_complete_latitudeSourceGaps {a φ : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6) (φ_pos : 0 < φ) (φ_bound : φ ≤ 0.0848 * √a)
    (radius : ∀ q ∈ slopes, ‖q‖ ≤ tan φ)
    (span : ∀ r : Root, let exit := (R.rootHeadingChart r (R.rootExitDirection r)).arg
      let lo := R.rootWindowStart r
      max (lo + H.width) exit - min lo exit ≤ π / 2 - 0.235 * a) :
    ∃ (level : ℝ) (higher : ∀ v : V, (G).height (p v) < level),
      ∃ (contour : (D[level,higher]).BoundaryContour (F[level,higher]).retain)
        (starts : (D[level,higher]).contourOriginalVertex Sel[level,higher] contour 0 ∈
          (F[level,higher]).parents.roots),
      (D[level,higher]).contourOriginalVertex Sel[level,higher] contour
          (Fin.last contour.length) ∈ (F[level,higher]).parents.roots ∧
      (∀ v : (D[level,higher]).Vertex Set.univ,
        0 < (D[level,higher]).interiorAngularDefect Set.univ v →
        ∃ e : (D[level,higher]).PositiveContourSource Sel[level,higher] contour,
          (D[level,higher]).positiveContourVertex Sel[level,higher] contour e = v) ∧
      ∀ e : (D[level,higher]).PositiveContourSource Sel[level,higher] contour,
        OrientedBankGap ((F[level,higher]).contourSourceRay contour starts e)
          ((F[level,higher]).contourSourceOpenedRay contour starts e) ∧
        ∀ k : Fin ((D[level,higher]).positiveContourBankLength Sel[level,higher] contour e),
          let bank := (F[level,higher]).contourSourceRay contour starts e
          0 < inner ℝ (bank.chain.vertex k.succ.castSucc - bank.start) (bank.chain.edge k.succ) := by
  obtain ⟨level, higher⟩ := exists_truncation_level
    (K := K) (slopes := slopes) (seed := seed) (B := B) (compact := compact) (nonempty := nonempty)
  obtain ⟨contour, starts, ends, coverage⟩ := R.exists_fineMesh_completeSourceContour level M higher
  have a_le : a ≤ 1 := by linarith only [small, pi_lt_d4]
  have sqrt_le : √a ≤ 1 := by simpa only [sqrt_one] using sqrt_le_sqrt a_le
  have tilt_small : φ ≤ 0.0848 :=
    φ_bound.trans ((mul_le_mul_of_nonneg_left sqrt_le (by norm_num)).trans_eq (mul_one _))
  have tilt_acute : φ < π / 2 := by linarith only [tilt_small, pi_gt_three]
  have cos_lower : 3 / 4 ≤ cos φ := by
    have φ_sq := pow_le_pow_left₀ φ_pos.le tilt_small 2
    linarith only [φ_sq, one_sub_sq_div_two_le_cos (x := φ)]
  let σ := 0.235 * a
  let γ := sin σ
  obtain ⟨_, _, γ_low, γ_high, flat⟩ :=
    latitude_three_exit_tilt_bounds positive small φ_pos.le φ_bound
  have γ_pos : 0 < γ := (mul_pos (by norm_num) positive).trans γ_low
  have error := (sharp_acuteCone_development_threshold γ_pos γ_high φ_pos.le flat
    (sqrt_nonneg 2) (le_refl (√(2 : ℝ)))).1
  let T := T[level,higher]
  let Q := T.roof (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M higher)
  have tilted : Q.TiltBound φ := by
    intro f
    let i := T.support f
    change cos φ ≤ (M.plane i).normal 2
    exact SpatialPlane.ofGraph_normal_height_of_slope_radius φ_pos tilt_acute _ _
      (radius _ (M.included i.val i.property))
  refine ⟨level, higher, contour, starts, ends, coverage, ?_⟩
  intro e
  exact R.contourSource_acute_gap level M higher contour starts e
    (show π / 2 - σ < π / 2 by dsimp only [σ]; linarith only [positive])
    γ_pos (by rw [cos_pi_div_two_sub]) span φ_pos tilt_acute cos_lower tilted error

end Unfoldings.ConvexRoof.ThreeExitComponentRouting
