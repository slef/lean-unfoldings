module

public import Unfoldings.FewestNets.ThreeExitContourGraft
public import Unfoldings.Roof.AffineFloorSharpWindows
public import Unfoldings.Roof.SharpBankCone
public import Unfoldings.Roof.PotentialContourAcuteGap
public import Unfoldings.FewestNets.ThreeExitSourceGaps

/-! The actual three-exit source gaps use the sharp heading allowance. -/

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

local instance sharpSourceIndexFintype (level : ℝ) (higher : ∀ v : V, (G).height (p v) < level) :
    Fintype (T[level,higher]).Index := @Fintype.ofFinite _ (T[level,higher]).finite

variable (level : ℝ)

local notation "Q[" level "," higher "]" => SpatialEnvelope.FloorMesh.roof T[level,higher]
  (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M higher)

set_option maxHeartbeats 3600000 in
/-- All links of the actual saved source bank and of its new opening lie in a common acute cone. -/
theorem contourSource_common_acuteCone
    (higher : ∀ v : V, (G).height (p v) < level)
    (contour : (D[level,higher]).BoundaryContour (F[level,higher]).retain)
    (starts : (D[level,higher]).contourOriginalVertex (Sel[level,higher]) contour 0 ∈ (F[level,higher]).parents.roots)
    (event : (D[level,higher]).PositiveContourSource (Sel[level,higher]) contour)
    {width φ Ω : ℝ} (φ_nonneg : 0 ≤ φ) (φ_small : φ < π / 2) (Ω_nonneg : 0 ≤ Ω)
    (tilt : ∀ i, cos φ ≤ (M.plane i).normal 2)
    (curvature : ∀ {A : Type} {eq : A → Plane →ᵃ[ℝ] ℝ}
      (L : (T[level,higher]).LineRefinement eq),
      letI : Fintype L.mesh.Index := @Fintype.ofFinite _ L.mesh.finite
      L.mesh.pairedComplex.totalInteriorAngularDefect Set.univ ≤ Ω)
    (roof_curvature : (D[level,higher]).totalInteriorAngularDefect Set.univ ≤ Ω)
    (span : ∀ r : Root, let exit := (R.rootHeadingChart r (R.rootExitDirection r)).arg
      let lo := R.rootWindowStart r
      max (lo + H.width) exit - min lo exit ≤ width)
    (acute : width + (2 * (2 * arcsin (tan (φ / 2) ^ 2)) + 2 * φ * sin φ + Ω) + Ω < π / 2) :
    ∃ center : ℝ, ((F[level,higher]).contourSourceRay contour starts event).InAcuteCone center ∧
      ((F[level,higher]).contourSourceOpenedRay contour starts event).InAcuteCone center := by
  let bank := (F[level,higher]).contourSourceBankChain contour starts event
  let source := (D[level,higher]).positiveContourVertex (Sel[level,higher]) contour event
  let n := (D[level,higher]).positiveContourBankLength (Sel[level,higher]) contour event
  let P := (Q[level,higher]).folding.projectedBoundaryChain bank
  let δ := (D[level,higher]).interiorAngularDefect Set.univ source
  let budget := 2 * (2 * arcsin (tan (φ / 2) ^ 2)) + 2 * φ * sin φ + Ω
  obtain ⟨r, headings⟩ := R.exists_root_window_for_fine_history level higher (Nat.succ_pos n) P
    (R.contourSourceBankChain_aligned level M higher contour starts event)
  let E := R.rootHeadingChart r
  let exit := (E (R.rootExitDirection r)).arg
  let lo := min (R.rootWindowStart r) exit
  let hi := max (R.rootWindowStart r + H.width) exit
  have within (i : Fin (n + 1)) : (E (P.edge i)).arg ∈ Set.Icc lo hi := by
    rcases headings i with stem | terminal
    · exact ⟨(min_le_left _ _).trans stem.1, stem.2.trans (le_max_left _ _)⟩
    · rw [terminal]
      exact ⟨min_le_right _ _, le_max_right _ _⟩
  have project_width : hi - lo ≤ width := span r
  have sine := Real.sin_nonneg_of_nonneg_of_le_pi φ_nonneg (by linarith only [φ_small, pi_pos])
  have angle : 0 ≤ arcsin (tan (φ / 2) ^ 2) := Real.arcsin_nonneg.mpr (sq_nonneg _)
  have budget_nonneg : 0 ≤ budget := by dsimp only [budget]; positivity
  have small : hi - lo < π / 2 := by linarith only [project_width, acute, budget_nonneg, Ω_nonneg]
  let θ := (lo + hi) / 2 + π / 4
  let axis := E.symm (polarRay θ)
  have unit : ‖axis‖ = 1 := (E.symm.norm_map _).trans (norm_polarRay _)
  have forward (i : Fin (n + 1)) : 0 < inner ℝ axis (P.edge i) :=
    (headingControls_pos E ((Q[level,higher]).projectedBoundaryChain_edge_ne_zero bank i) small (within i)).1
  have internal (i : Fin n) :
      (Q[level,higher]).projectedVertex ((D[level,higher]).vertexForgetCuts (Set.subset_univ _)
        ((D[level,higher]).boundaryEndVertex _ (bank.point i.succ))) ∈ interior (Q[level,higher]).footprint := by
    apply ((Q[level,higher]).projectedVertex_mem_interior_iff _).mpr
    intro boundary
    have root := (F[level,higher]).boundary_roots boundary
    rw [(F[level,higher]).contourSourceBankChain_original contour starts event i.succ] at root
    exact (F[level,higher]).parents.iterate_lt_distanceToRoot_not_mem source
      (by rw [(D[level,higher]).positiveContourBank_span (Sel[level,higher]) contour event]; exact i.succ.isLt) root
  have oscillation (i j : Fin (n + 1)) :
      |(Q[level,higher]).projectedMetricHeadingError bank i - (Q[level,higher]).projectedMetricHeadingError bank j| ≤ budget := by
    have ordered (i j : Fin (n + 1)) (before : i ≤ j) :
        |(Q[level,higher]).projectedMetricHeadingError bank i - (Q[level,higher]).projectedMetricHeadingError bank j| ≤ budget :=
      (T[level,higher]).abs_projectedMetricHeadingError_sub_le_sharp_of_direction
        (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M higher)
        bank axis unit forward ((F[level,higher]).contourSourceBankChain_cut contour starts event) internal
        φ_nonneg φ_small Ω_nonneg tilt curvature i j before
    rcases le_total i j with before | after
    · exact ordered i j before
    · rw [abs_sub_comm]; exact ordered j i after
  have defect : δ ≤ Ω := (by
    simpa only [Finset.sum_singleton] using (Q[level,higher]).sum_interiorAngularDefect_le_totalCurvature {source}
    : δ ≤ (D[level,higher]).totalInteriorAngularDefect Set.univ).trans roof_curvature
  apply (Q[level,higher]).exists_common_acuteCone_of_headingOscillation bank E within oscillation event.property.2.le
  change hi - lo + budget + δ < π / 2
  exact (add_le_add (add_le_add project_width le_rfl) defect).trans_lt acute

end Unfoldings.ConvexRoof.ThreeExitComponentRouting
