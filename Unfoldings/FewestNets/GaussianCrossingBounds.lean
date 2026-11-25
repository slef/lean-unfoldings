module

public import Unfoldings.FewestNets.GaussianCentralCancellation
public import Unfoldings.FewestNets.GaussianEndpointCharges
public import Unfoldings.FewestNets.SingleCellAreaBudget

/-! The two diameter regimes bound an actual Gaussian cell's signed charge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets SpatialRotation MeasureTheory SphericalSelectorBoundary InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)
  {J : Type*} [Fintype J] {region : Set Space} {B : SphericalSelectorBoundary J region}
  (M : MetricData B) (a : C.Vertex Set.univ)

local notation "site" => F.gaussianSiteOfVertex a
local notation "cell" => F.gaussianCell site

/-- The expected charge is averaged equally between the two orientation classes. -/
def meanMovedGaussianCharge (N : F.SupportingNormals) (region : Set Space)
    (a : C.Vertex Set.univ) (first second : C.Seam) : ℝ :=
  ((∫ g, gaussianSignedCharge N (movedSiteFlag region false g) a first second ∂probability) +
    (∫ g, gaussianSignedCharge N (movedSiteFlag region true g) a first second ∂probability)) / 2

open Classical in
/-- The residual perimeter uses genuine sides and omits the two original marks. -/
def gaussianResidualPerimeter (N : F.SupportingNormals) (a : C.Vertex Set.univ)
    (first second : C.Seam) : ℝ :=
  ∑ s ∈ gaussianArcSeams N a \ {first, second},
    angle (N.normal (C.left s).face) (N.normal (C.right s).face)

open Classical in
include P in
set_option maxHeartbeats 1300000 in
/-- In a small cell the normalized sum of the individual endpoint reaches controls the charge. -/
theorem meanMovedGaussianCharge_le_of_small_diameter
    (extreme : (site : Space) ∈ F.vertexHull.extremePoints ℝ)
    {d : ℝ} (nonneg : 0 ≤ d) (small : d < M.separation)
    (diameter : ∀ x ∈ cell, ∀ y ∈ cell, angle x y ≤ d)
    {first second : C.Seam} (different : first ≠ second)
    (marks : {first, second} ⊆ gaussianArcSeams N a) :
    meanMovedGaussianCharge N region a first second ≤
      ((∑ j : J × Bool, M.endpointFactor j.1 j.2) / π) *
        (gaussianResidualPerimeter N a first second * d) / (8 * π) := by
  let central := M.centralSet cell d
  let reach (j : J × Bool) := M.endpointFactor j.1 j.2 * d
  choose flip stable fixes negates using fun j => M.exists_centralSet_flip cell nonneg j
  have stable_false (j : J) (g : SpatialRotation) :
      g ∈ central false j ↔ g * flip j ∈ central true j := stable j g false
  have negates_false (j : J) (g : SpatialRotation) (x : Space) :
      B.form j ((orthogonalIsometry (g * flip j) true).symm x) =
        -B.form j ((orthogonalIsometry g false).symm x) := negates j g false x
  have first_side : first ∈ gaussianArcSeams N a := marks (by simp)
  have second_side : second ∈ gaussianArcSeams N a := marks (by simp)
  have paired (j : J) := P.ae_gaussian_centralCharge_pair N M a extreme nonneg small diameter
    first_side second_side j (flip j) (stable_false j) (negates_false j)
  have appears (b : Bool) (g : SpatialRotation) (outside : g ∈ (⋃ j, central b j)ᶜ)
      (j : J) (y : Space) (side : y ∈ networkEdge B.endpoint j)
      (hit : orthogonalIsometry g b y ∈ cell) :
      ∃ k : Bool, angle (B.endpoint j k) y ≤ reach (j, k) := by
    by_contra! far
    have inside := (M.mem_centralSet_iff cell nonneg b j g).mpr ⟨y, side, hit, far⟩
    exact outside (Set.mem_iUnion.mpr ⟨j, inside⟩)
  have estimate := P.mean_movedGaussianCharge_le_of_reaches N M a different
    (marks.trans (Finset.filter_subset _ _)) central
    (M.measurableSet_centralSet cell (F.isCompact_gaussianCell site).isClosed d)
    (M.pairwise_disjoint_centralSets cell nonneg small diameter) flip
    (fun j => Filter.Eventually.of_forall (stable_false j)) paired reach
    (fun j => mul_nonneg (M.endpointFactor_pos j.1 j.2).le nonneg)
    (fun b => Filter.Eventually.of_forall (appears b))
  change meanMovedGaussianCharge N region a first second ≤
    gaussianResidualPerimeter N a first second * (∑ j, reach j) / (8 * π ^ 2) at estimate
  refine estimate.trans_eq ?_
  simp only [reach, ← Finset.sum_mul]
  field_simp [pi_ne_zero]

open Classical in
include P M in
set_option maxHeartbeats 1000000 in
/-- The full selector perimeter bounds the charge for every diameter. -/
theorem meanMovedGaussianCharge_le_of_perimeter
    {first second : C.Seam} (different : first ≠ second)
    (marks : {first, second} ⊆ incidentSeams a) :
    meanMovedGaussianCharge N region a first second ≤
      (∑ j, angle (B.endpoint j false) (B.endpoint j true)) *
        gaussianResidualPerimeter N a first second / (8 * π ^ 2) := by
  let central (_ : Bool) (_ : J) : Set SpatialRotation := ∅
  let reach (p : J × Bool) : ℝ := if p.2 then 0 else 2 * B.halfLength p.1
  have nonnegative (p : J × Bool) : 0 ≤ reach p := by
    rcases p with ⟨j, b⟩
    cases b
    · exact mul_nonneg (by norm_num) (B.halfLength_nonneg j)
    · exact le_rfl
  have available (j : J) (y : Space)
      (side : y ∈ networkEdge B.endpoint j) :
      ∃ k : Bool, angle (B.endpoint j k) y ≤ reach (j, k) := by
    rw [← M.sidePoint_image j] at side
    obtain ⟨t, ht, rfl⟩ := side
    refine ⟨false, ?_⟩
    rw [M.angle_endpoint_sidePoint j false ht]
    change t + B.halfLength j ≤ 2 * B.halfLength j
    linarith only [ht.2]
  have estimate := P.mean_movedGaussianCharge_le_of_reaches N M a different marks
    central (fun _ _ => MeasurableSet.empty)
    (fun _ _ _ _ => by simp [central])
    (fun _ => 1) (fun _ => Filter.Eventually.of_forall (fun _ => by simp [central]))
    (fun _ => Filter.Eventually.of_forall (fun _ h => False.elim h))
    reach nonnegative
    (fun _ => Filter.Eventually.of_forall (fun _ _ j y side _ => available j y side))
  change meanMovedGaussianCharge N region a first second ≤
    gaussianResidualPerimeter N a first second * (∑ j, reach j) / (8 * π ^ 2) at estimate
  have sum : (∑ p, reach p) = ∑ j : J, angle (B.endpoint j false) (B.endpoint j true) := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, reach, Bool.false_eq_true, ite_false, ite_true, zero_add]
    apply Finset.sum_congr rfl
    intro j _
    unfold halfLength
    ring
  rw [sum, mul_comm] at estimate
  exact estimate

open Classical in
include P in
set_option maxHeartbeats 1500000 in
/-- Fixed marks at every original vertex bound the rotation-averaged signed
charge by that vertex's Gaussian area share. -/
theorem exists_marks_meanMovedGaussianCharge_le_area
    {eta : ℝ} (eta_pos : 0 < eta) (eta_small : eta ≤ π / 2)
    (min_angle : ∀ f i, eta ≤ (C.triangle f).cornerAngle i) :
    ∃ first second : C.Seam,
      meanMovedGaussianCharge N region a first second ≤
        (2 / (cos (M.separation / 2) ^ 2 * sin eta) * M.crossingBudget) *
          (solidAngleMeasure.real cell / (4 * π)) := by
  have sine : 0 < sin eta := sin_pos_of_pos_of_lt_pi eta_pos (by linarith only [eta_small, pi_pos])
  let S₀ := (∑ j : J × Bool, M.endpointFactor j.1 j.2) / π
  let L := ∑ j : J, angle (B.endpoint j false) (B.endpoint j true)
  have S₀_nonneg : 0 ≤ S₀ := div_nonneg
    (Finset.sum_nonneg (fun j _ => (M.endpointFactor_pos j.1 j.2).le)) pi_pos.le
  have L_nonneg : 0 ≤ L := Finset.sum_nonneg fun j _ => angle_nonneg _ _
  have area_nonneg : 0 ≤ solidAngleMeasure.real cell := ENNReal.toReal_nonneg
  by_cases extreme : (site : Space) ∈ F.vertexHull.extremePoints ℝ
  · obtain ⟨d, first, second, nonneg, diameter, different, marks, big, small⟩ :=
      P.exists_gaussian_marks_of_extreme N a extreme eta_pos eta_small min_angle
    refine ⟨first, second, ?_⟩
    have localized := P.meanMovedGaussianCharge_le_of_small_diameter N M a extreme nonneg
    have perimeter := P.meanMovedGaussianCharge_le_of_perimeter N M a different
      (marks.trans (Finset.filter_subset _ _))
    exact singleCellCharge_le_area S₀_nonneg L_nonneg M.separation_pos
      (M.separation_small.trans (by norm_num)) sine nonneg area_nonneg small big
      (fun narrow => localized narrow diameter different marks) (fun _ => perimeter)
  · obtain ⟨first, second, different, marks, covered⟩ :=
      P.exists_gaussian_marks_of_nonextreme N a extreme
    refine ⟨first, second, le_trans (b := (0 : ℝ)) ?_ ?_⟩
    · have integral_nonpos (b : Bool) :
          (∫ g, gaussianSignedCharge N (movedSiteFlag region b g) a first second ∂probability) ≤ 0 :=
        integral_nonpos (fun g => gaussianSignedCharge_nonpos_of_covered N _ a different marks covered)
      exact div_nonpos_of_nonpos_of_nonneg (add_nonpos (integral_nonpos false) (integral_nonpos true))
        (by norm_num)
    · have budget : 0 ≤ M.crossingBudget := S₀_nonneg.trans (le_max_left _ _)
      exact mul_nonneg
        (mul_nonneg (div_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) sine.le)) budget)
        (div_nonneg area_nonneg (by positivity))

end Unfoldings.SpatialFolding.ConvexBoundary
