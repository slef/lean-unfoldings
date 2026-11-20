module

public import Unfoldings.FewestNets.NormalVoronoi
public import Unfoldings.FewestNets.NetworkCrossings
public import Unfoldings.Geometry.EquatorialMinorArc

/-! A minor-arc cover of Voronoi walls supplies all changed-side witnesses. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry MeasureTheory SpatialRotation

/-- Given the actual minor-arc carriers of a finite wall cover, express those
carriers in Crofton coordinates. Every side with two distinct strict Voronoi
labels then yields a crossing of that network almost surely. -/
theorem exists_frames_ae_crossings_of_voronoi_wall_cover
    {I J : Type*} [Finite I] [Nonempty I] [Finite J] (site : I → Space)
    (injective : Function.Injective site)
    (start finish : J → Space) (start_unit : ∀ j, ‖start j‖ = 1)
    (finish_unit : ∀ j, ‖finish j‖ = 1)
    (positive : ∀ j, 0 < angle (start j) (finish j))
    (small : ∀ j, angle (start j) (finish j) < Real.pi)
    (walls : voronoiWalls site ⊆ ⋃ j, closedMinorArc (start j) (finish j))
    {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (not_antipodal : u + v ≠ 0) :
    ∃ frame : J → SpatialRotation,
      (∀ j, linear (frame j) '' equatorialArc (angle (start j) (finish j) / 2) =
        closedMinorArc (start j) (finish j)) ∧
      ∀ᵐ g ∂probability, ∀ {i j : I}, i ≠ j →
        u ∈ strictVoronoiCone (fun k => linear g (site k)) i →
        v ∈ strictVoronoiCone (fun k => linear g (site k)) j →
        ∃ k, g ∈ arcCrossingEvent u v (frame k) (angle (start k) (finish k) / 2) := by
  classical
  choose frame hframe using
    fun j => exists_frame_closedMinorArc (start_unit j) (finish_unit j) (positive j) (small j)
  refine ⟨frame, hframe, ?_⟩
  let cell (g : SpatialRotation) := strictVoronoiCone (fun k => linear g (site k))
  let radius (j : J) := angle (start j) (finish j) / 2
  filter_upwards [ae_crossing_witness_of_cell_coverage cell frame radius hu hv not_antipodal]
    with g witness
  have rot_inj : Function.Injective (fun k => linear g (site k)) :=
    (isometry g).injective.comp injective
  apply witness (fun j => strictVoronoiCone_isOpen _ j)
    (strictVoronoiCone_pairwise_disjoint _ rot_inj)
  intro x hx
  have x_sphere := closedMinorArc_subset_sphere hu hv not_antipodal hx
  rcases sphere_subset_strictVoronoiCone_union_walls (fun k => linear g (site k)) rot_inj
      x_sphere with good | on_wall
  · exact Or.inl good
  · rw [← image_voronoiWalls] at on_wall
    obtain ⟨y, hy, rfl⟩ := on_wall
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (walls hy)
    exact Or.inr (Set.mem_iUnion.mpr ⟨k, ⟨y, (hframe k).symm ▸ hk, rfl⟩⟩)

end Unfoldings.FewestNets
