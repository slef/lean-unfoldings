module

public import Unfoldings.Roof.AdaptiveBankSubhistories
public import Unfoldings.Roof.CompatibleContourSourceOnlyGaps
public import Unfoldings.Roof.SpatialEnvelopeInteriorBanks

/-! The adaptive radial bounds supply the actual source-only gaps of the cut roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {L : Set Plane} {r margin η : ℝ}
  (R : K.CompatibleAdaptiveRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary L r margin η)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)
  (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
  (positive : 0 < r) (disk : Metric.closedBall (0 : Plane) r ⊆ L)
  {b : ℝ} (bound_pos : 0 < b) (ratio : r ≤ b) (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)

local notation "common" => R.asCommonPotentialRouting positive disk bound_pos ratio upper
local notation "inner_disk" => Metric.ball_subset_closedBall.trans (disk.trans R.within)
local notation "βnonnegative" => Real.arccos_nonneg (r / b)
local notation "βacute" => Real.arccos_lt_pi_div_two.mpr (div_pos positive bound_pos)
local notation "T" => K.compatibleCutMesh compact nonempty common no_boundary level higher M
  positive inner_disk
local notation "fine" => SpatialEnvelope.ConstrainedTriangulation.toTriangulation T
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty common no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty common level higher M
local notation "Fcut" => K.compatibleMeshForest compact nonempty common no_boundary level higher
  M positive inner_disk βnonnegative βacute
local notation "D" => SpatialEnvelope.Triangulation.pairedComplex fine
local notation "Selection" => PotentialCutForest.selection Fcut

local instance adaptiveContourGapIndexFintype : Fintype (T).Index := @Fintype.ofFinite _ (T).finite

local notation "First[" contour "," starts "," e "]" =>
  K.compatibleContourSourceBank compact nonempty common no_boundary level higher M positive
    inner_disk βnonnegative βacute contour starts e

local notation "Opened[" contour "," starts "," e "]" =>
  K.compatibleContourSourceOnlyBank compact nonempty common no_boundary level higher M positive
    inner_disk βnonnegative βacute contour starts e

open Classical in
/-- The reference bank is rolled in the current retained mesh, so it already
includes the saved fans. At a fresh source, its second bank is a single rotation
by the defect. The sharp estimate controls the actual saved reference bank. -/
theorem adaptiveContourSourceOnly_gap
    {φ γ A : ℝ} (tilt_pos : 0 < φ) (small_phi : φ < π / 2)
    (height_bound : (3 : ℝ) / 4 ≤ cos φ) (normal : ∀ i, cos φ ≤ (M.plane i).normal 2)
    (gamma_pos : 0 < γ) (gamma_le : γ ≤ 1) (interior_margin : γ ≤ margin)
    (exterior_margin : γ ≤ η) (length_bound : b / r ≤ A)
    (small : radialBlockError (cos φ)⁻¹ (shallowDevelopmentHeading φ) A
      (sqrt (1 - γ ^ 2)) π < γ)
    (contour : (D).BoundaryContour ((D).selectedRetain Selection))
    (starts : (D).contourOriginalVertex Selection contour 0 ∈ (Fcut).parents.roots)
    (event : (D).PositiveContourSource Selection contour) :
    OrientedBankGap First[contour,starts,event] Opened[contour,starts,event] ∧
      ∀ k : Fin ((D).positiveContourBankLength Selection contour event),
        let bank := First[contour,starts,event]
        0 < inner ℝ (bank.chain.vertex k.succ.castSucc - bank.start) (bank.chain.edge k.succ) := by
  let Q := (fine).roof conforming inside
  let cap := (fine).normalizedCap conforming inside
  let m := (D).positiveContourBankLength Selection contour event
  let span := (D).positiveContourBank_span Selection contour event
  let first := First[contour,starts,event]
  let chain := K.compatibleMeshFreshSourceBankChain compact nonempty common no_boundary level higher
    M positive inner_disk βnonnegative βacute contour starts event.val event.property.1 m span
  let path := (D).boundaryChainRoll chain
  have routed := K.compatibleMeshFreshSourceBankChain_follows compact nonempty common no_boundary
    level higher M positive inner_disk βnonnegative βacute contour starts event.val event.property.1
    m span
  have cut (i : Fin (m + 1)) : ¬ (D).IsBoundaryEdge Set.univ ((D).germEdge (chain.point i).val) :=
    (fine).boundaryEnd_is_cut_of_projected_mem_interior conforming inside _ (chain.point i)
      (K.compatibleMeshFreshSourceBankChain_starts_interior compact nonempty common no_boundary
        level higher M positive inner_disk βnonnegative βacute contour starts event.val
        event.property.1 m span i)
  have tilt : Q.TiltBound φ := fun i => normal ((fine).support i)
  obtain ⟨_, radial⟩ := adaptive_bank_subhistories compact nonempty R no_boundary positive disk
    bound_pos ratio upper Q tilt_pos small_phi height_bound tilt gamma_pos gamma_le interior_margin
    exterior_margin length_bound chain cut routed small
  let E := radialBlockError (cos φ)⁻¹ (shallowDevelopmentHeading φ) A (sqrt (1 - γ ^ 2)) π
  let d := (γ - E) / (1 + E)
  have cos_pos : 0 < cos φ := (by norm_num : (0 : ℝ) < 3 / 4).trans_le height_bound
  have e_nonneg : 0 ≤ E := radialBlockError_nonneg ((one_le_inv₀ cos_pos).mpr (cos_le_one φ))
    (shallowDevelopmentHeading_nonneg_of_cos tilt_pos.le
      (by linarith only [small_phi, pi_pos]) cos_pos)
    ((div_nonneg bound_pos.le positive.le).trans length_bound) (sqrt_nonneg _) pi_pos
  have d_pos : 0 < d := div_pos (sub_pos.mpr small) (by positivity)
  have outward : path.Outward := fun j i before =>
    (mul_nonneg d_pos.le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans (radial j i before)
  have path_genuine (i : Fin (m + 1)) : path.edge i ≠ 0 :=
    (D).boundaryChainRoll_edge_ne_zero chain i
  have ray_outward : first.Outward := path.terminalEdgeRay_outward outward
  have ray_ne : first.direction ≠ 0 := path_genuine (Fin.last m)
  let vertex := (D).positiveContourVertex Selection contour event
  let defect := (D).interiorAngularDefect Set.univ vertex
  have defect_le : defect ≤ (D).totalInteriorAngularDefect Set.univ := by
    simpa only [Finset.sum_singleton] using (cap).sum_interiorAngularDefect_le_totalCurvature {vertex}
  have total := (cap).totalCurvature_le_shallowDevelopmentCurvature tilt_pos.le small_phi
    ((fine).normalizedCap_tilt conforming inside normal)
  have curvature_small : shallowDevelopmentCurvature φ < π := by
    have h := mul_le_mul_of_nonneg_left (sub_le_sub_left height_bound 1)
      (show 0 ≤ 2 * π by positivity)
    unfold shallowDevelopmentCurvature
    linarith only [h, pi_pos]
  have defect_small := (defect_le.trans total).trans_lt curvature_small
  refine ⟨first.orientedGap_rotateSuffix_zero ray_outward ray_ne event.property.2 defect_small, ?_⟩
  intro k
  let i := k.succ
  have radial_from := (path.radiallyMonotone_iff_outward.mpr outward) 0
  have radii := path.vertex_radius_strictMono_of_radial (path.vertex 0) radial_from path_genuine
  have later : (0 : Fin (m + 2)) < i.castSucc := by
    change 0 < k.val + 1
    omega
  have dist_pos : 0 < dist (path.vertex 0) (path.vertex i.castSucc) :=
    (show (0 : ℝ) ≤ dist (path.vertex 0) (path.vertex 0) from dist_nonneg).trans_lt (radii later)
  have norm_pos : 0 < ‖path.vertex i.castSucc - path.vertex 0‖ :=
    by simpa only [dist_eq_norm'] using dist_pos
  exact (mul_pos d_pos (mul_pos norm_pos (norm_pos_iff.mpr (path_genuine i)))).trans_le
    (radial 0 i (Nat.zero_le _))

end Unfoldings.ConvexRoof
