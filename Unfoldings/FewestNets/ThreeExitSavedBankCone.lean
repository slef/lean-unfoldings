module

public import Unfoldings.FewestNets.ThreeExitSharpSourceGaps
public import Unfoldings.FewestNets.ThreeExitGraftFlatness

/-! The saved acute bank suffices for the source-only opening used by the three-exit graft. -/

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

local instance savedBankIndexFintype (level : ℝ)
    (higher : ∀ v : V, (G).height (p v) < level) : Fintype (T[level,higher]).Index :=
  @Fintype.ofFinite _ (T[level,higher]).finite

local notation "Roof[" level "," higher "]" => SpatialEnvelope.FloorMesh.roof T[level,higher]
  (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M higher)

local notation "Bank[" L "," h "," c "," s "," e "]" =>
  PotentialCutForest.contourSourceBankChain F[L,h] c s e

local notation "Event[" L "," h "," c "]" =>
  TriangleComplex.PositiveContourSource D[L,h] Sel[L,h] c

local notation "Length[" L "," h "," c "," e "]" =>
  TriangleComplex.positiveContourBankLength D[L,h] Sel[L,h] c e

/-- The comparison on a forward saved bank is a bound on the real heading
differences of all of its subhistories. -/
def SavedHeadingBound (error : ℝ) : Prop :=
  ∀ (level : ℝ) (higher : ∀ v : V, (G).height (p v) < level)
    (contour : (D[level,higher]).BoundaryContour (F[level,higher]).retain)
    (starts : (D[level,higher]).contourOriginalVertex (Sel[level,higher]) contour 0 ∈
      (F[level,higher]).parents.roots)
    (event : Event[level,higher,contour]), let bank := Bank[level,higher,contour,starts,event]
    let Q := Roof[level,higher]
    ∀ (axis : Plane), ‖axis‖ = 1 →
      (∀ i, 0 < inner ℝ axis ((Q.folding.projectedBoundaryChain bank).edge i)) →
      ∀ i j, |Q.projectedMetricHeadingError bank i - Q.projectedMetricHeadingError bank j| ≤ error

set_option maxHeartbeats 1200000 in
/-- An original history of width strictly below a right angle after intrinsic
heading comparison gives an actual saved acute bank. Only its source is rotated. -/
theorem contourSource_saved_acuteCone_of_bound
    (level : ℝ) (higher : ∀ v : V, (G).height (p v) < level)
    (contour : (D[level,higher]).BoundaryContour (F[level,higher]).retain)
    (starts : (D[level,higher]).contourOriginalVertex (Sel[level,higher]) contour 0 ∈
      (F[level,higher]).parents.roots)
    (event : Event[level,higher,contour]) {width error : ℝ} (error_nonneg : 0 ≤ error)
    (span : ∀ r : Root, let exit := (R.rootHeadingChart r (R.rootExitDirection r)).arg
      let lo := R.rootWindowStart r
      max (lo + H.width) exit - min lo exit ≤ width)
    (comparison : R.SavedHeadingBound M error)
    (acute : width + error < π / 2) :
    ∃ center : ℝ, ((F[level,higher]).contourSourceRay contour starts event).InAcuteCone center := by
  let bank := Bank[level,higher,contour,starts,event]
  let n := Length[level,higher,contour,event]
  let Q := Roof[level,higher]
  let P := Q.folding.projectedBoundaryChain bank
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
  have width_le : hi - lo ≤ width := span r
  have small : hi - lo < π / 2 := by linarith only [width_le, acute, error_nonneg]
  let θ := (lo + hi) / 2 + π / 4
  let axis := E.symm (polarRay θ)
  have unit : ‖axis‖ = 1 := (E.symm.norm_map _).trans (norm_polarRay _)
  have forward (i : Fin (n + 1)) : 0 < inner ℝ axis (P.edge i) :=
    (headingControls_pos E (Q.projectedBoundaryChain_edge_ne_zero bank i) small (within i)).1
  obtain ⟨center, cone, _⟩ := Q.exists_common_acuteCone_of_headingOscillation bank E within
    (comparison level higher contour starts event axis unit forward) (opening := 0) le_rfl
    (by linarith only [width_le, acute])
  exact ⟨center, cone⟩


/-- A uniformly accurate saved-bank heading estimate yields an original-edge net.
The source opening itself consumes no additional angular width. -/
theorem hasOriginalEdgeNet_of_savedHeadingBound {width error : ℝ}
    (selected : K.normalSlope seed ∈ slopes) (error_nonneg : 0 ≤ error)
    (span : ∀ r : Root, let exit := (R.rootHeadingChart r (R.rootExitDirection r)).arg
      let lo := R.rootWindowStart r
      max (lo + H.width) exit - min lo exit ≤ width)
    (comparison : R.SavedHeadingBound M error) (acute : width + error < π / 2)
    (curvature : ∀ (level : ℝ) (higher : ∀ v : V, (G).height (p v) < level),
      (D[level,higher]).totalInteriorAngularDefect Set.univ < π) :
    C.HasOriginalEdgeNet U := by
  obtain ⟨level, higher⟩ := exists_truncation_level
    (K := K) (slopes := slopes) (seed := seed) (B := B) (compact := compact) (nonempty := nonempty)
  obtain ⟨contour, starts, ends, _⟩ := R.exists_fineMesh_completeSourceContour level M higher
  have gap (e : Event[level,higher,contour]) :
      OrientedBankGap ((F[level,higher]).contourSourceRay contour starts e)
        ((F[level,higher]).contourSourceOpenedRay contour starts e) ∧
      ∀ k : Fin Length[level,higher,contour,e],
        let bank := (F[level,higher]).contourSourceRay contour starts e
        0 < inner ℝ (bank.chain.vertex k.succ.castSucc - bank.start) (bank.chain.edge k.succ) := by
    obtain ⟨center, cone⟩ := R.contourSource_saved_acuteCone_of_bound M level higher contour starts e
      error_nonneg span comparison acute
    exact (F[level,higher]).contourSource_gap_of_acuteCone contour starts e (curvature level higher) cone
  let S : FloorWindowModel.SourceContour (R := R) (M := M) (level := level) :=
    ⟨higher, contour, starts, fun e => (gap e).1⟩
  let L := R.floorWindowModel level M S.higher
  exact L.hasOriginalEdgeNet_of_complete_contour S selected ends (fun e => (gap e).2)

end Unfoldings.ConvexRoof.ThreeExitComponentRouting
