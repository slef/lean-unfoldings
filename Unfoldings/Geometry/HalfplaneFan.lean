module

public import Unfoldings.Geometry.PlanarAngleAddition
public import Unfoldings.Geometry.PlanarConjugation
public import Unfoldings.Geometry.ChainConstruction

/-! A consistently oriented ray chain in a closed halfplane has no angular wraparound. -/

@[expose] public section

namespace Unfoldings

variable {n : ℕ}

/-- The angular distance between endpoints is bounded by the actual chain's angular length. -/
theorem angle_endpoint_le_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ray : Fin (n + 2) → E) (first : ray 0 ≠ 0) :
    InnerProductGeometry.angle (ray 0) (ray (Fin.last (n + 1))) ≤
      ∑ i : Fin (n + 1), InnerProductGeometry.angle (ray i.castSucc) (ray i.succ) := by
  let angle (i : Fin (n + 1)) := InnerProductGeometry.angle (ray i.castSucc) (ray i.succ)
  have prefix_bound (i : Fin (n + 2)) :
      InnerProductGeometry.angle (ray 0) (ray i) ≤ Fin.partialSum angle i := by
    refine Fin.induction ?_ (fun k previous => ?_) i
    · simp only [Fin.partialSum_zero, InnerProductGeometry.angle_self first, le_refl]
    · rw [Fin.partialSum_succ]
      exact (InnerProductGeometry.angle_le_angle_add_angle
        (ray 0) (ray k.castSucc) (ray k.succ)).trans (add_le_add previous (le_refl (angle k)))
  have total : Fin.partialSum angle (Fin.last (n + 1)) = ∑ i, angle i := by
    change ((List.ofFn angle).take (n + 1)).sum = ∑ i, angle i
    rw [List.take_of_length_le (by simp only [List.length_ofFn]; exact le_rfl), List.sum_ofFn]
  simpa only [total] using prefix_bound (Fin.last (n + 1))

/-- Positive turns in the halfplane based at the first ray have exact endpoint angle. -/
theorem sum_ray_angles_eq_endpoint_of_positive (ray : Fin (n + 2) → Plane)
    (genuine : ∀ i, ray i ≠ 0)
    (positive : ∀ i : Fin (n + 1), 0 < orient 0 (ray i.castSucc) (ray i.succ))
    (halfplane : ∀ i, 0 ≤ orient 0 (ray 0) (ray i)) :
    (∑ i : Fin (n + 1), InnerProductGeometry.angle (ray i.castSucc) (ray i.succ)) =
      InnerProductGeometry.angle (ray 0) (ray (Fin.last (n + 1))) := by
  let angle (i : Fin (n + 1)) := InnerProductGeometry.angle (ray i.castSucc) (ray i.succ)
  have prefix_eq (i : Fin (n + 2)) :
      Fin.partialSum angle i = InnerProductGeometry.angle (ray 0) (ray i) := by
    refine Fin.induction ?_ (fun k previous => ?_) i
    · simp only [Fin.partialSum_zero, InnerProductGeometry.angle_self (genuine 0)]
    · rw [Fin.partialSum_succ, previous]
      exact (angle_add_of_orient_nonneg (genuine 0) (genuine k.castSucc)
        (halfplane k.castSucc) (halfplane k.succ) (positive k)).symm
  have total : Fin.partialSum angle (Fin.last (n + 1)) = ∑ i, angle i := by
    change ((List.ofFn angle).take (n + 1)).sum = ∑ i, angle i
    rw [List.take_of_length_le (by simp only [List.length_ofFn]; exact le_rfl), List.sum_ofFn]
  simpa only [total] using prefix_eq (Fin.last (n + 1))

/-- Reflection handles either orientation without identifying bank contact with crossing. -/
theorem sum_ray_angles_eq_endpoint (ray : Fin (n + 2) → Plane)
    (genuine : ∀ i, ray i ≠ 0)
    (nonzero : ∀ i : Fin (n + 1), orient 0 (ray i.castSucc) (ray i.succ) ≠ 0)
    (consistent : ∀ i : Fin (n + 1),
      (0 < orient 0 (ray i.castSucc) (ray i.succ)) ↔
        0 < orient 0 (ray (0 : Fin (n + 1)).castSucc) (ray (0 : Fin (n + 1)).succ))
    (halfplane : ∀ i, 0 ≤ orient 0 (ray 0) (ray i) *
      orient 0 (ray (0 : Fin (n + 1)).castSucc) (ray (0 : Fin (n + 1)).succ)) :
    (∑ i : Fin (n + 1), InnerProductGeometry.angle (ray i.castSucc) (ray i.succ)) =
      InnerProductGeometry.angle (ray 0) (ray (Fin.last (n + 1))) := by
  by_cases first : 0 < orient 0 (ray (0 : Fin (n + 1)).castSucc) (ray (0 : Fin (n + 1)).succ)
  · exact sum_ray_angles_eq_endpoint_of_positive ray genuine
      (fun i => (consistent i).mpr first)
      (fun i => by nlinarith [halfplane i])
  · have initial : orient 0 (ray (0 : Fin (n + 1)).castSucc)
        (ray (0 : Fin (n + 1)).succ) < 0 := lt_of_le_of_ne (le_of_not_gt first) (nonzero 0)
    have reflected := sum_ray_angles_eq_endpoint_of_positive
      (fun i => planeConjugation (ray i))
      (fun i => by simpa only [map_zero] using planeConjugation.injective.ne (genuine i))
      (fun i => by
        rw [orient_planeConjugation]
        exact neg_pos.mpr (lt_of_le_of_ne
          (le_of_not_gt (fun h => first ((consistent i).mp h))) (nonzero i)))
      (fun i => by
        rw [orient_planeConjugation]
        have nonpos : orient 0 (ray 0) (ray i) ≤ 0 := by nlinarith [halfplane i]
        exact neg_nonneg.mpr nonpos)
    have angles (x y : Plane) : InnerProductGeometry.angle (planeConjugation x)
        (planeConjugation y) = InnerProductGeometry.angle x y :=
      planeConjugation.toLinearIsometry.angle_map x y
    simpa only [angles] using reflected

end Unfoldings
