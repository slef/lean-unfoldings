module

public import Unfoldings.Geometry.MeshProgress

/-! Every interior mesh vertex has an edge entering any prescribed open halfplane. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Filter Topology

/-- A single positive linear coordinate requires no acute-triangle hypothesis. -/
theorem exists_mesh_halfplane_edge {Face : Type*} [Finite Face] (triangle : Face → Triangle)
    (region : Set Plane) (cover : region ⊆ ⋃ f, (triangle f).carrier) (center : Plane)
    (inside : center ∈ interior region)
    (corner : ∀ f, center ∈ (triangle f).carrier → ∃ i, (triangle f).vertex i = center)
    (height : Plane →ₗ[ℝ] ℝ) (direction : Plane) (positive : 0 < height direction) :
    ∃ f i, (triangle f).vertex i = center ∧
      (0 < height ((triangle f).vertex (Triangle.next i) - center) ∨
        0 < height ((triangle f).vertex (Triangle.next (Triangle.next i)) - center)) := by
  have star := eventually_piece_contains_center (fun f => (triangle f).carrier)
    (fun f => (triangle f).compact_carrier.isClosed) center
  have near : {p | p ∈ region ∧ ∀ f, p ∈ (triangle f).carrier →
      center ∈ (triangle f).carrier} ∈ 𝓝 center := by
    filter_upwards [star, isOpen_interior.mem_nhds inside] with p hp interior
    exact ⟨interior_subset interior, hp⟩
  obtain ⟨t, tpos, present, star⟩ := exists_positive_ray_mem center direction _ near
  obtain ⟨f, in_face⟩ := Set.mem_iUnion.mp (cover present)
  obtain ⟨i, vertex⟩ := corner f (star f in_face)
  refine ⟨f, i, vertex, ?_⟩
  have coefficients := (triangle f).carrier_subset_cornerWedge i in_face
  have combination := (triangle f).reconstruct_corner i (center + t • direction)
  have expression :
      (triangle f).coord (Triangle.next i) (center + t • direction) •
          ((triangle f).vertex (Triangle.next i) - center) +
        (triangle f).coord (Triangle.next (Triangle.next i)) (center + t • direction) •
          ((triangle f).vertex (Triangle.next (Triangle.next i)) - center) = t • direction := by
    have equation := congrArg (fun p : Plane => p - center) combination
    simpa only [Triangle.cornerCombination, vertex, add_sub_cancel_right,
      add_sub_cancel_left] using equation
  have ahead := congrArg height expression
  simp only [map_add, map_smul, smul_eq_mul] at ahead
  by_contra neither
  have nonpositive :
      height ((triangle f).vertex (Triangle.next i) - center) ≤ 0 ∧
        height ((triangle f).vertex (Triangle.next (Triangle.next i)) - center) ≤ 0 := by
    simpa only [not_or, not_lt] using neither
  have bound := add_nonpos (mul_nonpos_of_nonneg_of_nonpos coefficients.1 nonpositive.1)
    (mul_nonpos_of_nonneg_of_nonpos coefficients.2 nonpositive.2)
  rw [ahead] at bound
  exact (not_lt_of_ge bound) (mul_pos tpos positive)

end Unfoldings
