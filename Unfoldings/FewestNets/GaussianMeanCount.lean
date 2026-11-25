module

public import Unfoldings.FewestNets.GaussianCrossingBounds

/-! Sum the actual Gaussian charges over the original polyhedron. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets SpatialRotation MeasureTheory SphericalSelectorBoundary InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

private theorem integral_movedGaussianCharge (region : Set Space)
    (b : Bool) (a : C.Vertex Set.univ) (first second : C.Seam) :
    (∫ g, gaussianSignedCharge N (movedSiteFlag region b g) a first second ∂probability) =
      ∫ g, gaussianSignedCharge N (fun x => siteFlag region b x g) a first second ∂probability := by
  let f (g : SpatialRotation) := gaussianSignedCharge N (fun x => siteFlag region b x g)
    a first second
  change (∫ g, f (g⁻¹) ∂probability) = ∫ g, f g ∂probability
  exact (Measure.measurePreserving_inv probability).integral_comp
    (MeasurableEquiv.inv SpatialRotation).measurableEmbedding f

include P in
set_option maxHeartbeats 1600000 in
/-- The selector's expected number of original components is its uniform area
term plus its normalized crossing budget times the common acute-angle factor. -/
theorem mean_gaussianSelectedCount_le {J : Type*} [Fintype J]
    {region : Set Space} {B : SphericalSelectorBoundary J region} (M : MetricData B)
    (q : Space) (unit : ‖q‖ = 1) (hemisphere : ∀ x ∈ region, 0 < inner ℝ q x)
    {eta : ℝ} (eta_pos : 0 < eta) (eta_small : eta ≤ π / 2)
    (min_angle : ∀ f i, eta ≤ (C.triangle f).cornerAngle i) :
    ((∫ g, gaussianSelectedCount N region false g ∂probability) +
      (∫ g, gaussianSelectedCount N region true g ∂probability)) / 2 ≤
      2 * uniformSphere.real region +
        2 / (cos (M.separation / 2) ^ 2 * sin eta) * M.crossingBudget := by
  classical
  let K := 2 / (cos (M.separation / 2) ^ 2 * sin eta) * M.crossingBudget
  let A (a : C.Vertex Set.univ) := solidAngleMeasure.real (F.gaussianCell (F.gaussianSiteOfVertex a))
  choose first second bound using fun a : C.Vertex Set.univ =>
    P.exists_marks_meanMovedGaussianCharge_le_area N M a eta_pos eta_small min_angle
  have total := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => bound a)
  change (∑ a, meanMovedGaussianCharge N region a (first a) (second a)) ≤
    ∑ a, K * (A a / (4 * π)) at total
  have area : (∑ a, A a) = 4 * π := P.sum_original_gaussianCellArea
  rw [← Finset.mul_sum, ← Finset.sum_div, area, div_self (by positivity : 4 * π ≠ 0), mul_one] at total
  have each (b : Bool) := P.integral_gaussianSelectedCount_eq N region B.sphericalConvex B.isClosed
    q unit hemisphere b first second
  have sum_as_average :
      (∑ a, meanMovedGaussianCharge N region a (first a) (second a)) =
      ((∑ a, ∫ g, gaussianSignedCharge N (fun x => siteFlag region false x g)
        a (first a) (second a) ∂probability) +
        (∑ a, ∫ g, gaussianSignedCharge N (fun x => siteFlag region true x g)
          a (first a) (second a) ∂probability)) / 2 := by
    simp only [meanMovedGaussianCharge, integral_movedGaussianCharge N,
      ← Finset.sum_div, Finset.sum_add_distrib]
  rw [sum_as_average] at total
  rw [each false, each true]
  change _ ≤ 2 * uniformSphere.real region + K
  linarith only [total]

end Unfoldings.SpatialFolding.ConvexBoundary
