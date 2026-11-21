module

public import Unfoldings.FewestNets.GaussianExpectedCharge

/-! An admissible rotation with a bounded number of original face components. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets SpatialRotation MeasureTheory InnerProductGeometry Real
open scoped BigOperators

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

include P in
/-- A spherical Voronoi network has a rotation with the explicit component
bound, and every selected whole-face component is an intrinsic disk. -/
theorem exists_rotation_with_bounded_voronoi_components
    {I J : Type*} [Finite I] [Nonempty I] [Fintype J]
    {site : I → Space} {endpoint : J → Bool → Space} {separation psi : ℝ}
    (H : VoronoiNetwork site endpoint separation psi)
    {eta : ℝ} (positive : 0 < eta) (minimum : ∀ f i, eta ≤ (C.triangle f).cornerAngle i) :
    ∃ g : SpatialRotation,
      (∀ f, N.normal f ∈ strictVoronoiCone (fun j => linear g (site j))
        (voronoiLabel site (N.normal f) g)) ∧
      let label (f : Face) := voronoiLabel site (N.normal f) g
      (Nat.card (C.labeledSeamGraph label).ConnectedComponent : ℝ) ≤
        2 + componentCoefficient (Fintype.card J) (networkLength endpoint) separation psi /
          sin (eta / 2) ∧
      ∀ c : (C.labeledSeamGraph label).ConnectedComponent, C.RestrictionIsDisk c.supp := by
  let label (g : SpatialRotation) (f : Face) := voronoiLabel site (N.normal f) g
  let good (g : SpatialRotation) := ∀ f : Face,
    N.normal f ∈ strictVoronoiCone (fun j => linear g (site j)) (label g f)
  let bad := {g | ¬good g}
  have ae_good : ∀ᵐ g ∂probability, good g :=
    ae_voronoiLabel_mem_strict H.siteInjective N.normal N.unit
  have null : probability bad = 0 := ae_iff.mp ae_good
  let charge (a : C.Vertex Set.univ) (g : SpatialRotation) :=
    componentCharge (labelCutDegree (label g) a)
  let total (g : SpatialRotation) := 2 + ∑ a : C.Vertex Set.univ, charge a g
  let coefficient := componentCoefficient (Fintype.card J) (networkLength endpoint) separation psi /
    sin (eta / 2)
  let area (a : C.Vertex Set.univ) :=
    solidAngleMeasure.real (F.gaussianCell (F.gaussianSiteOfVertex a))
  have summed_area : (∑ a, area a) = 4 * π := by
    change (∑ a : C.Vertex Set.univ,
      (solidAngleMeasure (F.gaussianCell (F.gaussianSiteOfVertex a))).toReal) = _
    simp only [F.solidAngle_gaussianCell]
    exact (Equiv.sum_comp P.vertexEquivGaussianSite
      (fun i => (solidAngleMeasure (F.gaussianCone i)).toReal)).trans (F.sum_gaussianArea P)
  have integrable (a : C.Vertex Set.univ) : Integrable (charge a) probability :=
    integrable_gaussian_voronoi_charge N site H.siteInjective a
  have integrable_sum : Integrable (fun g => ∑ a, charge a g) probability :=
    integrable_finsetSum _ fun a _ => integrable a
  have integrable_total : Integrable total probability := (integrable_const 2).add integrable_sum
  have average : (∫ g, total g ∂probability) ≤ 2 + coefficient := by
    unfold total
    rw [integral_add (integrable_const 2) integrable_sum, integral_const]
    simp only [probReal_univ, one_smul]
    rw [integral_finsetSum Finset.univ (fun a _ => integrable a)]
    have expected (a : C.Vertex Set.univ) :
        (∫ g, charge a g ∂probability) ≤ coefficient * (area a / (4 * π)) :=
      P.expected_gaussian_voronoi_charge_le_area N H positive minimum a
    have bound := Finset.sum_le_sum (s := (Finset.univ : Finset (C.Vertex Set.univ)))
      (fun a _ => expected a)
    rw [← Finset.mul_sum, ← Finset.sum_div, summed_area,
      div_self (by positivity : 4 * π ≠ 0), mul_one] at bound
    exact add_le_add_right bound 2
  obtain ⟨g, valid, below⟩ := exists_notMem_null_le_integral integrable_total null
  have at_g : good g := Classical.not_not.mp valid
  let cells := sphericalVoronoiCell (fun j => linear g (site j))
  let center (i : I) := linear g (site i)
  have unit (i : I) : ‖center i‖ = 1 := ((isometry g).norm_map _).trans (H.siteUnit i)
  have hemisphere : ∀ i, ∀ x ∈ cells i, 0 < inner ℝ (center i) x := H.rotated_hemisphere g
  have assign : ∀ f i, N.normal f ∈ cells i ↔ label g f = i := fun f i =>
    mem_sphericalVoronoiCell_iff_voronoiLabel H.siteInjective g (N.unit f) (at_g f) i
  have convex (i : I) : SphericalConvex (cells i) := sphericalConvex_sphericalVoronoiCell _ i
  have closed (i : I) : IsClosed (cells i) := isClosed_sphericalVoronoiCell _ i
  have exact_count : (Nat.card (C.labeledSeamGraph (label g)).ConnectedComponent : ℝ) = total g :=
    P.normal_component_count_eq_two_add_sum_vertex_charges N cells center unit hemisphere
      (label g) assign convex closed
  refine ⟨g, at_g, ?_, ?_⟩
  · exact exact_count.le.trans (below.trans average)
  · exact P.restrictionIsDisk_of_normal_cells N cells center unit hemisphere
      (label g) assign convex closed

end Unfoldings.SpatialFolding.ConvexBoundary
