module

public import Unfoldings.FewestNets.IcosahedronRadialIntersections
public import Unfoldings.Geometry.RadialTriangleGauge

/-! The linear piece of the radial gauge on each fine mesh triangle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open scoped BigOperators

def meshGauge {q : ℕ} (hq : 0 < q) (t : MeshFace q) : Space →ₗ[ℝ] ℝ :=
  radialTriangleGauge (linearIndependent_inscribedCorners hq t)

theorem meshGauge_corner {q : ℕ} (hq : 0 < q) (t : MeshFace q) (k : Fin 3) :
    meshGauge hq t (inscribedCorners t k) = 1 :=
  radialTriangleGauge_corner _ k

/-- The linear pieces agree wherever their closed cones meet. -/
theorem meshGauge_eq_of_mem_cones {q : ℕ} (hq : 0 < q) (t s : MeshFace q) {x : Space}
    (ht : x ∈ radialTriangleCone (inscribedCorners t))
    (hs : x ∈ radialTriangleCone (inscribedCorners s)) :
    meshGauge hq t x = meshGauge hq s x := by
  by_cases zero : x = 0
  · simp [zero]
  obtain ⟨w, nonnegative, eq, shared⟩ := exists_shared_corner_expansion hq t s zero ht hs
  rw [eq, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [map_smul, meshGauge_corner]
  by_cases positive : 0 < w k
  · obtain ⟨j, hj⟩ := shared k positive
    rw [← hj, meshGauge_corner]
  · rw [le_antisymm (le_of_not_gt positive) (nonnegative k), zero_smul, zero_smul]

/-- A common point outside the finitely many corner rays gives two common corners. -/
theorem exists_two_shared_corners {q : ℕ} (hq : 0 < q) (t s : MeshFace q) {x : Space}
    (off : ∀ k : Fin 3, ∀ r : ℝ, x ≠ r • inscribedCorners t k)
    (ht : x ∈ radialTriangleCone (inscribedCorners t))
    (hs : x ∈ radialTriangleCone (inscribedCorners s)) :
    ∃ i j : Fin 3, i ≠ j ∧ inscribedCorners t i ∈ Set.range (inscribedCorners s) ∧
      inscribedCorners t j ∈ Set.range (inscribedCorners s) := by
  have nonzero : x ≠ 0 := by simpa only [zero_smul] using off 0 0
  obtain ⟨w, nonnegative, eq, shared⟩ := exists_shared_corner_expansion hq t s nonzero ht hs
  have some : ∃ i, 0 < w i := by
    by_contra! absent
    have zero (k : Fin 3) : w k = 0 := le_antisymm (absent k) (nonnegative k)
    exact nonzero (by simp [eq, zero])
  obtain ⟨i, positive⟩ := some
  have second : ∃ j, i ≠ j ∧ 0 < w j := by
    by_contra! absent
    apply off i (w i)
    rw [eq, Finset.sum_eq_single i]
    · intro b _ other
      rw [le_antisymm (absent b other.symm) (nonnegative b), zero_smul]
    · simp
  obtain ⟨j, ij, positive'⟩ := second
  exact ⟨i, j, ij, shared i positive, shared j positive'⟩

end Unfoldings.FewestNets.Icosahedron
