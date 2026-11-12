module

public import Unfoldings.Cap.RadialStripPhysicalMap
public import Unfoldings.Cap.ProjectedDenseSeparation
public import Unfoldings.Topology.FiniteRadiusAvoidance

/-! Global strip-circle separation implies separation of actual developed face interiors. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)
  {t : ℝ} (positive : 0 < t) (small : t < 1) (D : FacewiseDevelopment C N.retain)
  (calibration : Plane ≃ₗᵢ[ℝ] ℂ) {ε cutoff : ℝ}
  (P : ∀ i : FiveSector, (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
  (traces : ∀ i : FiveSector, ∀ cell : {S : MonotoneStrip // S ∈ (P i).cells},
    N.RadialStripTraceData positive small D calibration i cell.val ε cutoff)

/-- The geometric input still required here is separation of all strip slices
in the common developed plane. Finite exceptional radii and physical subdivision
walls then cannot hide open overlap of any two actual face interiors. -/
theorem face_interiors_disjoint_of_circle_separation {U : Set Plane}
    (region_open : IsOpen U)
    (inside : U ⊆ sectorSweepInterior positive small source cutoff)
    (bound : ℝ) {exception : Set ℝ} (finite : exception.Finite)
    (image_bound : ∀ p ∈ U, ‖D.projectedMap K p - D.projectedMap K source‖ < bound)
    (separated : ∀ first last : Σ i : FiveSector, {S : MonotoneStrip // S ∈ (P i).cells},
      first ≠ last → ∀ radius ∈ Set.Ioo (0 : ℝ) bound, radius ∉ exception →
      Disjoint
        ((traces first.1 first.2).outputFrame.symm ''
          ((traces first.1 first.2).value '' first.2.val.openSlab 0 cutoff ∩
            {z | ‖z - (traces first.1 first.2).center‖ = radius}))
        ((traces last.1 last.2).outputFrame.symm ''
          ((traces last.1 last.2).value '' last.2.val.openSlab 0 cutoff ∩
            {z | ‖z - (traces last.1 last.2).center‖ = radius}))) :
    Pairwise (fun f g : Face =>
      Disjoint (D.projectedPlacement K f '' (interior (K.projectedTriangle f).carrier ∩ U))
        (D.projectedPlacement K g '' (interior (K.projectedTriangle g).carrier ∩ U))) := by
  let Cell := Σ i : FiveSector, {S : MonotoneStrip // S ∈ (P i).cells}
  let data := fun cell : Cell => traces cell.1 cell.2
  have pair_separation (first last : Cell) (different : first ≠ last) :
      Disjoint (D.projectedMap K '' (data first).physicalDomain ∩
        Metric.ball (D.projectedMap K source) bound)
        (D.projectedMap K '' (data last).physicalDomain ∩
          Metric.ball (D.projectedMap K source) bound) := by
    apply disjoint_open_in_ball_of_circle_disjoint_off_finite
      (data first).isOpen_image_physicalDomain (data last).isOpen_image_physicalDomain
      (D.projectedMap K source) bound finite
    intro radius radius_bounds outside
    rw [(data first).circle_image_physicalDomain, (data last).circle_image_physicalDomain]
    exact separated first last different radius radius_bounds outside
  have injective : Set.InjOn (D.projectedMap K)
      (sectorWaterfallRegular positive small source P ∩ U) := by
    intro p first q last equal
    obtain ⟨i, S, cell, p_member⟩ := sectorWaterfallRegular_mem_openSlab positive small source P
      first.1 (inside first.2)
    obtain ⟨j, T, other_cell, q_member⟩ := sectorWaterfallRegular_mem_openSlab
      positive small source P last.1 (inside last.2)
    let a : Cell := ⟨i, ⟨S, cell⟩⟩
    let b : Cell := ⟨j, ⟨T, other_cell⟩⟩
    have p_domain : p ∈ (data a).physicalDomain := p_member
    have q_domain : q ∈ (data b).physicalDomain := q_member
    by_cases same : a = b
    · have domains := congrArg (fun c : Cell => (data c).physicalDomain) same
      rw [← domains] at q_domain
      exact (data a).physical_injective p_domain q_domain equal
    · have p_ball : D.projectedMap K p ∈ Metric.ball (D.projectedMap K source) bound := by
        rw [Metric.mem_ball, dist_eq_norm]
        exact image_bound p first.2
      exact (Set.disjoint_left.mp (pair_separation a b same)
        ⟨⟨p, p_domain, rfl⟩, p_ball⟩ ⟨⟨q, q_domain, equal.symm⟩, p_ball⟩).elim
  exact fun _ _ different => D.projected_face_interiors_disjoint_of_dense_injective K
    (isOpen_sectorWaterfallRegular positive small source P)
    (dense_sectorWaterfallRegular positive small source P) region_open injective different

end Unfoldings.ConvexCap.RadialCutForest
