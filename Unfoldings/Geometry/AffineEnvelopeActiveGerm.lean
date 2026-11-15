module

public import Unfoldings.Geometry.AffineEnvelope

/-! Active planes alone determine the local germ of a finite lower envelope. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AffineEnvelope

variable {I : Type*} [Fintype I] [Nonempty I] (support : I → Plane →ᵃ[ℝ] ℝ)

/-- A support minimizing all currently active planes on a region minimizes the full
finite envelope there in a neighborhood. Inactive planes are excluded by strict gaps. -/
theorem exists_radius_height_eq_on_region (i : I) (p : Plane)
    (active : height support p = support i p) (region : Set Plane)
    (dominates : ∀ j, height support p = support j p →
      ∀ z ∈ region, support i z ≤ support j z) :
    ∃ r : ℝ, 0 < r ∧ ∀ z, dist z p < r → z ∈ region → height support z = support i z := by
  classical
  let good : Set Plane := ⋂ j, {z | height support p = support j p ∨ support i z < support j z}
  have open_good : IsOpen good := by
    apply isOpen_iInter_of_finite
    intro j
    by_cases is_active : height support p = support j p
    · simpa only [is_active, true_or, Set.ofPred_true] using isOpen_univ (X := Plane)
    · simpa only [is_active, false_or] using isOpen_lt
        (support i).continuous_of_finiteDimensional (support j).continuous_of_finiteDimensional
  have inside : p ∈ good := by
    apply Set.mem_iInter.mpr
    intro j
    by_cases is_active : height support p = support j p
    · exact Or.inl is_active
    · exact Or.inr (active ▸ lt_of_le_of_ne (height_le support p j) is_active)
  obtain ⟨r, positive, near⟩ := Metric.isOpen_iff.mp open_good p inside
  refine ⟨r, positive, ?_⟩
  intro z close member
  apply (mem_cell_iff support i z).mp
  intro j
  have comparison := Set.mem_iInter.mp (near (Metric.mem_ball.mpr close)) j
  exact comparison.elim (fun is_active => dominates j is_active z member) le_of_lt

end Unfoldings.AffineEnvelope
