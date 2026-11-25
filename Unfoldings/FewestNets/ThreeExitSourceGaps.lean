module

public import Unfoldings.FewestNets.ThreeExitMesh
public import Unfoldings.FewestNets.ThreeExitAcuteDevelopment
public import Unfoldings.Roof.PotentialContourGap

/-! The actual positive contour sources of a fine three-exit cut have concrete gaps. -/

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
local notation "Root" => {r // r ∈ R.stems.choice.parents.roots}

variable (level : ℝ)
variable (M : SlopeEnvelope.FiniteSlopeModel
  (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty))

local notation "p" => (fun v : V => K.projectedVertex (Subtype.val v))

local notation "Mesh[" h "]" => R.fineMesh level M h
local notation "D[" h "]" => SpatialEnvelope.FloorMesh.pairedComplex (Mesh[h])

local instance threeExitSourceGapsFintype (higher : ∀ v : V, (G).height (p v) < level) :
    Fintype (R.fineMesh level M higher).Index :=
  @Fintype.ofFinite _ (R.fineMesh level M higher).finite

local notation "Q[" h "]" => SpatialEnvelope.FloorMesh.roof (Mesh[h])
  (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M h)
local notation "F[" h "]" => R.fineMeshForest level M h
local notation "Selection[" h "]" => PotentialCutForest.selection (F[h])

/-- The entire saved physical bank, including its last outgoing link, follows
the oriented embedding of the same three-exit forest. -/
theorem contourSourceBankChain_aligned
    (higher : ∀ v : V, (G).height (p v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Selection[higher] contour 0 ∈ (F[higher]).parents.roots)
    (event : (D[higher]).PositiveContourSource Selection[higher] contour)
    (i : Fin (((D[higher]).positiveContourBankLength Selection[higher] contour event) + 1)) :
    let P := (Q[higher]).folding.projectedBoundaryChain ((F[higher]).contourSourceBankChain contour starts event)
    Nonempty ((R.truncatedEmbedding level higher).OrientedSubsegment
      (P.vertex i.castSucc) (P.vertex i.succ)) := by
  let source := (D[higher]).positiveContourVertex Selection[higher] contour event
  let length := (D[higher]).positiveContourBankLength Selection[higher] contour event
  let bank := (F[higher]).contourSourceBankChain contour starts event
  have same : (Q[higher]).folding.projectedBoundaryChain bank =
      R.fineMeshHistory level M higher source (length + 1) := by
    apply congrArg PolygonalChain.mk
    funext j
    exact (F[higher]).contourSourceBankChain_projected_vertex contour starts event j
  change Nonempty ((R.truncatedEmbedding level higher).OrientedSubsegment
    (((Q[higher]).folding.projectedBoundaryChain ((F[higher]).contourSourceBankChain contour starts event)).vertex i.castSucc)
    (((Q[higher]).folding.projectedBoundaryChain ((F[higher]).contourSourceBankChain contour starts event)).vertex i.succ))
  rw [same]
  exact R.fineMeshHistory_aligned level M higher source (length + 1)
    ((D[higher]).positiveContourBank_span Selection[higher] contour event).ge i

set_option maxHeartbeats 1800000 in
/-- Each positive source in the actual sweep opens a nonoverlapping gap, including
the genuine last exit ray and all its finite bends. -/
theorem contourSource_acute_gap
    (higher : ∀ v : V, (G).height (p v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Selection[higher] contour 0 ∈ (F[higher]).parents.roots)
    (event : (D[higher]).PositiveContourSource Selection[higher] contour)
    {width gamma phi : ℝ} (acute : width < π / 2) (gamma_pos : 0 < gamma)
    (γ_margin : gamma ≤ cos width)
    (span : ∀ r : Root,
      let exit := ((R.rootHeadingChart r) (R.rootExitDirection r)).arg
      let lo := R.rootWindowStart r
      max (lo + H.width) exit - min lo exit ≤ width)
    (tilt_pos : 0 < phi) (small_phi : phi < π / 2) (height_bound : (3 : ℝ) / 4 ≤ cos phi)
    (tilt : (Q[higher]).TiltBound phi) (small : acuteConeDevelopmentError phi (√2) < gamma) :
    OrientedBankGap ((F[higher]).contourSourceRay contour starts event)
      ((F[higher]).contourSourceOpenedRay contour starts event) ∧
      ∀ k : Fin ((D[higher]).positiveContourBankLength Selection[higher] contour event),
        let bank := (F[higher]).contourSourceRay contour starts event
        0 < inner ℝ (bank.chain.vertex k.succ.castSucc - bank.start) (bank.chain.edge k.succ) := by
  have bounds := R.sharp_threeExit_bank_subhistories level higher (Q[higher]) ((F[higher]).contourSourceBankChain contour starts event)
    ((F[higher]).contourSourceBankChain_cut contour starts event)
    (R.contourSourceBankChain_aligned level M higher contour starts event)
    acute gamma_pos γ_margin span tilt_pos small_phi height_bound tilt small
  have curvature := (Q[higher]).totalCurvature_le_shallowDevelopmentCurvature tilt_pos.le small_phi tilt
  have omega_bound : shallowDevelopmentCurvature phi < π := by
    have up := mul_le_mul_of_nonneg_left (sub_le_sub_left height_bound 1)
      (show 0 ≤ 2 * π by positivity)
    unfold shallowDevelopmentCurvature
    linarith only [up, pi_pos]
  have cos_pos : 0 < cos phi := (by norm_num : (0 : ℝ) < 3 / 4).trans_le height_bound
  have speed := (one_le_inv₀ cos_pos).mpr (cos_le_one phi)
  have heading := acuteConeDevelopmentHeading_nonneg tilt_pos.le
    (show phi ≤ π by linarith only [small_phi, pi_pos])
  have error_nonneg : 0 ≤ acuteConeDevelopmentError phi (√2) := by
    have diff : 0 ≤ (cos phi)⁻¹ - 1 := sub_nonneg.mpr speed
    unfold acuteConeDevelopmentError
    positivity
  have margin_pos : 0 < (gamma - acuteConeDevelopmentError phi (√2)) /
      (1 + acuteConeDevelopmentError phi (√2)) := div_pos (sub_pos.mpr small) (by positivity)
  exact (F[higher]).contourSource_gap contour starts event margin_pos (curvature.trans_lt omega_bound)
    bounds.2

end Unfoldings.ConvexRoof.ThreeExitComponentRouting
