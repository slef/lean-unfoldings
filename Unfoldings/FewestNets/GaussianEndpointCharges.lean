module

public import Unfoldings.FewestNets.GaussianSelectedExpectation
public import Unfoldings.FewestNets.GaussianSelectorCrossings
public import Unfoldings.FewestNets.SphericalSelectorFrames
public import Unfoldings.FewestNets.SingleCellAveragedCrossings

/-! Integrate the residual crossings of the original marked Gaussian cell. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets SingleCellCharge SpatialRotation MeasureTheory SphericalSelectorBoundary
  InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)
  {J : Type*} [Fintype J] {region : Set Space} {B : SphericalSelectorBoundary J region}
  (M : MetricData B) (a : C.Vertex Set.univ)

local notation "site" => F.gaussianSiteOfVertex a
local notation "cell" => F.gaussianCell site

set_option maxHeartbeats 600000 in
/-- The moved-selector charge is integrable just as in the pulled-back convention. -/
theorem integrable_movedGaussianCharge (region : Set Space) (measurable : MeasurableSet region)
    (b : Bool) (first second : C.Seam) :
    Integrable (fun g => gaussianSignedCharge N (movedSiteFlag region b g) a first second)
      probability := by
  let f (g : SpatialRotation) := gaussianSignedCharge N (fun x => siteFlag region b x g)
    a first second
  change Integrable (f ∘ fun g : SpatialRotation => g⁻¹) probability
  exact (Measure.measurePreserving_inv probability).integrable_comp_of_integrable
    (integrable_gaussianSignedCharge N measurable b a first second)

open Classical in
include P M in
set_option maxHeartbeats 1800000 in
/-- Once central contacts cancel, an endpoint reach for every remaining
contact gives the Crofton bound on the original unmarked Gaussian sides. -/
theorem mean_movedGaussianCharge_le_of_reaches
    {first second : C.Seam} (different : first ≠ second)
    (marks : {first, second} ⊆ incidentSeams a)
    (central : Bool → J → Set SpatialRotation) (measurable : ∀ b j, MeasurableSet (central b j))
    (disjoint : ∀ b, Pairwise fun i j => Disjoint (central b i) (central b j))
    (flip : J → SpatialRotation)
    (stable : ∀ j, ∀ᵐ g ∂probability, g ∈ central false j ↔ g * flip j ∈ central true j)
    (paired : ∀ j, ∀ᵐ g ∂probability, g ∈ central false j →
      gaussianSignedCharge N (movedSiteFlag region false g) a first second +
        gaussianSignedCharge N (movedSiteFlag region true (g * flip j)) a first second = 0)
    (reach : J × Bool → ℝ) (reach_nonneg : ∀ j, 0 ≤ reach j)
    (localizes : ∀ b, ∀ᵐ g ∂probability, g ∈ (⋃ j, central b j)ᶜ →
      ∀ j, ∀ y ∈ networkEdge B.endpoint j, orthogonalIsometry g b y ∈ cell →
        ∃ k : Bool, angle (B.endpoint j k) y ≤ reach (j, k)) :
    let S := ∑ s ∈ gaussianArcSeams N a \ {first, second},
      angle (N.normal (C.left s).face) (N.normal (C.right s).face)
    ((∫ g, gaussianSignedCharge N (movedSiteFlag region false g) a first second ∂probability) +
      (∫ g, gaussianSignedCharge N (movedSiteFlag region true g) a first second ∂probability)) / 2 ≤
      S * (∑ j, reach j) / (8 * π ^ 2) := by
  let Sides := gaussianArcSeams N a \ {first, second}
  let I := {s // s ∈ Sides}
  let firstNormal (s : C.Seam) := N.normal (C.left s).face
  let lastNormal (s : C.Seam) := N.normal (C.right s).face
  let ell (s : C.Seam) := angle (firstNormal s) (lastNormal s)
  let sign (b : Bool) : Space ≃ₗᵢ[ℝ] Space :=
    if b then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ Space
  have sign_placement (g : SpatialRotation) (b : Bool) (x : Space) :
      sign b (orthogonalIsometry g b x) = linear g x := by
    rw [orthogonalIsometry_apply]
    cases b
    · rfl
    · change -(-(linear g x)) = _
      rw [neg_neg]
  let u (b : Bool) (i : I) := sign b (firstNormal i.val)
  let v (b : Bool) (i : I) := sign b (lastNormal i.val)
  let changed (b : Bool) (g : SpatialRotation) (i : I) :=
    movedSiteFlag region b g (firstNormal i.val) ≠ movedSiteFlag region b g (lastNormal i.val)
  let charge (b : Bool) (g : SpatialRotation) :=
    gaussianSignedCharge N (movedSiteFlag region b g) a first second
  have hu (b : Bool) (i : I) : ‖u b i‖ = 1 :=
    ((sign b).norm_map _).trans (N.unit _)
  have hv (b : Bool) (i : I) : ‖v b i‖ = 1 :=
    ((sign b).norm_map _).trans (N.unit _)
  have incident (i : I) : i.val ∈ incidentSeams a :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp i.property).1).1
  have not_antipodal (b : Bool) (i : I) : u b i + v b i ≠ 0 := by
    intro zero
    apply P.gaussianSide_nonantipodal N a (incident i)
    apply (sign b).injective
    rw [map_add, map_zero]
    exact zero
  have reindex (f : C.Seam → ℝ) : (∑ i : I, f i.val) = ∑ s ∈ Sides, f s := by
    refine Finset.sum_bij (fun i _ => i.val) (fun i _ => i.property)
      (fun i _ j _ eq => Subtype.ext eq) (fun s hs => ⟨⟨s, hs⟩, Finset.mem_univ _, rfl⟩)
      (fun _ _ => rfl)
  have length (b : Bool) : (∑ i, angle (u b i) (v b i)) = ∑ s ∈ Sides, ell s := by
    calc
      _ = ∑ i : I, ell i.val := Finset.sum_congr rfl
        (fun i _ => (sign b).toLinearIsometry.angle_map _ _)
      _ = _ := reindex ell
  have pointwise (b : Bool) (g : SpatialRotation) :
      charge b g ≤ (∑ i, if changed b g i then (1 : ℝ) else 0) / 4 := by
    have bound := gaussianSignedCharge_le_unmarked N (movedSiteFlag region b g) a
      (marks (by simp : first ∈ ({first, second} : Finset C.Seam)))
      (marks (by simp : second ∈ ({first, second} : Finset C.Seam))) different
    change charge b g ≤ (∑ s ∈ Sides, crossing (seamMembership N (movedSiteFlag region b g) s)) / 4 at bound
    rw [← reindex] at bound
    convert bound using 2
    apply Finset.sum_congr rfl
    intro i _
    classical
    by_cases h : changed b g i
    · have neq : movedSiteFlag region b g (firstNormal i.val) ≠
          movedSiteFlag region b g (lastNormal i.val) := h
      simp only [h, ite_true, seamMembership, crossing, firstNormal, lastNormal, neq, ite_false]
    · have eq : movedSiteFlag region b g (firstNormal i.val) =
          movedSiteFlag region b g (lastNormal i.val) := not_ne_iff.mp h
      simp only [h, ite_false, seamMembership, crossing, firstNormal, lastNormal, eq, ite_true]
  refine mean_singleCellCharge_le_of_endpoint_witnesses charge
    (fun b => integrable_movedGaussianCharge N a region B.isClosed.measurableSet b first second)
    central measurable disjoint flip stable paired changed u v M.sideFrame B.halfLength
    hu hv not_antipodal B.halfLength_nonneg M.halfLength_small reach reach_nonneg
    (∑ s ∈ Sides, ell s) length (fun b => Filter.Eventually.of_forall (fun g _ => pointwise b g)) ?_
  intro b
  filter_upwards [P.ae_gaussian_selector_crossing N B a b, localizes b] with g crossing near
  intro outside i across
  obtain ⟨j, x, on_seam, on_side, in_cell⟩ := crossing i.val (incident i) across
  let T := orthogonalIsometry g b
  have moved : x ∈ T '' networkEdge B.endpoint j := by
    rw [networkEdge, image_closedMinorArc_linearIsometry]
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ on_side)
  obtain ⟨y, at_side, positioned⟩ := moved
  obtain ⟨k, close⟩ := near outside j y at_side (positioned.symm ▸ in_cell)
  have reflected : sign b x = linear g y := by
    rw [← positioned, sign_placement]
  refine ⟨(j, k), sign b x, ?_, ?_, ?_⟩
  · change sign b x ∈ openMinorArc (sign b (firstNormal i.val)) (sign b (lastNormal i.val))
    rw [← image_openMinorArc_linearIsometry]
    exact Set.mem_image_of_mem _ on_seam
  · rw [reflected, M.sideFrame_image_arc]
    exact Set.mem_image_of_mem _ at_side
  · change angle (linear g (linear (M.sideFrame j) (equatorPoint
      ((arcEndpointPhase (B.halfLength j) k : ℝ) : EquatorPhase)))) (sign b x) ≤ _
    rw [M.sideFrame_endpoint, reflected]
    exact ((isometry g).toLinearIsometry.angle_map _ _).trans_le close

end Unfoldings.SpatialFolding.ConvexBoundary
