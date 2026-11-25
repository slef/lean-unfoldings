module

public import Unfoldings.Geometry.AcuteChainExterior
public import Unfoldings.Geometry.AffineLevelInterior

/-! One of the two acute-cone closing disks leaves the opposite incident face outside. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n)
  (h k : Plane →L[ℝ] ℝ)
  (first : ∀ i, 0 < h (P.edge i)) (last : ∀ i, 0 < k (P.edge i))

include first last in
/-- The two choices of closure leave opposite transverse rays outside. A
regular adjacent body therefore has a point outside one of the two disks. -/
theorem adjacent_body_not_subset_one_twoLink_domain
    (nonempty : 0 < n) (joint : Function.Injective fun p => (h p, k p))
    (low high : Plane)
    (low_initial : h low ≤ h (P.vertex 0))
    (low_terminal : k (P.vertex (Fin.last n)) ≤ k low)
    (high_initial : k high ≤ k (P.vertex 0))
    (high_terminal : h (P.vertex (Fin.last n)) ≤ h high)
    {p x y : Plane} (bank : p ∈ Set.range P.path)
    (not_first : p ≠ P.vertex 0) (not_last : p ≠ P.vertex (Fin.last n))
    (S : Set Plane) (convex : Convex ℝ S) (full : (interior S).Nonempty)
    (on_boundary : p ∉ interior S) (x_in : x ∈ S) (y_in : y ∈ S)
    (x_below : h x + k x < h p + k p) (y_above : h p + k p < h y + k y) :
    (¬ S ⊆ PlanarTopology.closedJordanDomain (P.twoLinkClosure low)) ∨
      (¬ S ⊆ PlanarTopology.closedJordanDomain (P.twoLinkClosure high)) := by
  obtain ⟨q, in_body, level⟩ := exists_interior_point_of_linear_between
    convex full (h + k) x_in y_in x_below y_above
  let v := q - p
  have nonzero : v ≠ 0 := sub_ne_zero.mpr (fun same => on_boundary (same ▸ in_body))
  have across : h v + k v = 0 := by
    change h q + k q = h p + k p at level
    dsimp only [v]
    rw [map_sub, map_sub]
    linarith only [level]
  have h_ne : h v ≠ 0 := by
    intro zero
    have k_zero : k v = 0 := by linarith only [across, zero]
    apply nonzero
    apply joint
    exact Prod.ext (zero.trans (map_zero h).symm) (k_zero.trans (map_zero k).symm)
  have point : p + (1 : ℝ) • v = q := by simp [v]
  rcases lt_or_gt_of_ne h_ne with h_down | h_up
  · right
    intro contained
    have outside := P.acute_exterior_ray_avoids_domain high k h last first high_initial
      high_terminal nonempty bank not_first not_last
      (show 0 < k v by linarith only [across, h_down]) (by linarith only [across]) zero_lt_one
    exact outside (point ▸ contained (interior_subset in_body))
  · left
    intro contained
    have outside := P.acute_exterior_ray_avoids_domain low h k first last low_initial
      low_terminal nonempty bank not_first not_last h_up across zero_lt_one
    exact outside (point ▸ contained (interior_subset in_body))

end Unfoldings.PolygonalChain
