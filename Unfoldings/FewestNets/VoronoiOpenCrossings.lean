module

public import Unfoldings.FewestNets.VoronoiCrossings

/-! Almost surely changed sides cross the relative interiors of the network edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry MeasureTheory SpatialRotation

private theorem exists_normal_zero_on_openMinorArc {u v : Space} (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) :
    ∃ f : Space →L[ℝ] ℝ, f ≠ 0 ∧ ∀ x ∈ openMinorArc u v, f x = 0 := by
  obtain ⟨g, left, right⟩ := exists_centered_arc_rotation hu hv
  let n := linear g⁻¹ equatorPole
  have n_unit : ‖n‖ = 1 :=
    ((isometry g⁻¹).norm_map _).trans equatorPole_unit
  have map_inner (x : Space) : inner ℝ n x = inner ℝ equatorPole (linear g x) := by
    rw [← inner_linear g n x, show linear g n = equatorPole from linear_apply_inv g _]
  have left_zero : inner ℝ n u = 0 := by
    rw [map_inner, left, inner_equatorPole]
    rfl
  have right_zero : inner ℝ n v = 0 := by
    rw [map_inner, right, inner_equatorPole]
    rfl
  refine ⟨innerSL ℝ n, ?_, ?_⟩
  · intro equal
    have zero := DFunLike.congr_fun equal n
    change inner ℝ n n = 0 at zero
    rw [real_inner_self_eq_norm_sq, n_unit] at zero
    norm_num at zero
  · rintro _ ⟨t, ht, rfl⟩
    change inner ℝ n (NormedSpace.normalize _) = 0
    rw [NormedSpace.normalize, real_inner_smul_right, inner_add_right,
      real_inner_smul_right, real_inner_smul_right, left_zero, right_zero]
    ring

/-- Every changed side in a finite family has an interior intersection with a moving
Voronoi edge, once the closed network arcs cover the actual walls. -/
theorem ae_open_network_crossing_of_voronoi_labels
    {I J E : Type*} [Finite I] [Nonempty I] [Finite J] [Finite E]
    (site : I → Space) (injective : Function.Injective site)
    (start finish : J → Space) (start_unit : ∀ j, ‖start j‖ = 1)
    (finish_unit : ∀ j, ‖finish j‖ = 1)
    (positive : ∀ j, 0 < angle (start j) (finish j))
    (small : ∀ j, angle (start j) (finish j) < Real.pi)
    (walls : voronoiWalls site ⊆ ⋃ j, closedMinorArc (start j) (finish j))
    (u v : E → Space) (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1)
    (not_antipodal : ∀ i, u i + v i ≠ 0) :
    ∀ᵐ g ∂probability, ∀ i : E, ∀ ⦃a b : I⦄, a ≠ b →
      u i ∈ strictVoronoiCone (fun k => linear g (site k)) a →
      v i ∈ strictVoronoiCone (fun k => linear g (site k)) b →
      ∃ j x, x ∈ openMinorArc (u i) (v i) ∧
        x ∈ openMinorArc (linear g (start j)) (linear g (finish j)) := by
  classical
  choose normal nonzero vanishes using fun i => exists_normal_zero_on_openMinorArc (hu i) (hv i)
  have start_avoids := ae_avoids_finite_hyperplanes start start_unit normal nonzero
  have finish_avoids := ae_avoids_finite_hyperplanes finish finish_unit normal nonzero
  choose frame recognizes crosses using fun i =>
    exists_frames_ae_crossings_of_voronoi_wall_cover site injective start finish start_unit
      finish_unit positive small walls (hu i) (hv i) (not_antipodal i)
  have crossing := ae_all_iff.mpr crosses
  filter_upwards [crossing, start_avoids, finish_avoids] with g crossing start_off finish_off
  intro i a b diff left right
  obtain ⟨j, x, hx, _⟩ := crossing i diff left right
  obtain ⟨on_side, on_network⟩ := hx
  rw [recognizes i j, image_closedMinorArc] at on_network
  rcases Set.mem_insert_iff.mp on_network with first | rest
  · exact False.elim (start_off j i (first ▸ vanishes i x on_side))
  · rcases Set.mem_insert_iff.mp rest with last | interior
    · exact False.elim (finish_off j i (last ▸ vanishes i x on_side))
    · exact ⟨j, x, on_side, interior⟩

end Unfoldings.FewestNets
