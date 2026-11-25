module

public import Unfoldings.Basic
public import Mathlib.Geometry.Euclidean.Sphere.Basic

/-! Three distinct unit points on a positive affine level form a radial triangle basis. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Module

/-- A nonzero affine level turns affine independence of unit sites into
linear independence in the original ambient space. -/
theorem linearIndependent_unitChordTriangle_of_level
    (p : Fin 3 → Space) (unit : ∀ i, ‖p i‖ = 1) (different : Function.Injective p)
    (n : Space) {d : ℝ} (nonzero : d ≠ 0) (level : ∀ i, inner ℝ n (p i) = d) :
    LinearIndependent ℝ p := by
  let s := Metric.sphere (0 : Space) 1
  have spherical : EuclideanGeometry.Cospherical s :=
    ⟨0, 1, fun x hx => Metric.mem_sphere.mp hx⟩
  have contained : Set.range p ⊆ s := by
    rintro _ ⟨i, rfl⟩
    exact Metric.mem_sphere.mpr ((dist_zero_right _).trans (unit i))
  have independent := spherical.affineIndependent contained different
  rw [Fintype.linearIndependent_iff]
  intro weight combination i
  have image := congrArg (inner ℝ n) combination
  change (innerSL ℝ n) (∑ j, weight j • p j) = (innerSL ℝ n) 0 at image
  simp only [map_sum, map_smul, smul_eq_mul, map_zero] at image
  have total : (∑ j, weight j) * d = 0 := by
    rw [Finset.sum_mul]
    simpa only [show ∀ j, (innerSL ℝ n) (p j) = d from level] using image
  exact independent.eq_zero_of_sum_eq_zero ((mul_eq_zero.mp total).resolve_right nonzero)
    combination i (Finset.mem_univ i)

/-- A radial basis with precisely the three prescribed unit vertices. -/
theorem exists_basis_unitChordTriangle_of_level
    (p : Fin 3 → Space) (unit : ∀ i, ‖p i‖ = 1) (different : Function.Injective p)
    (n : Space) {d : ℝ} (nonzero : d ≠ 0) (level : ∀ i, inner ℝ n (p i) = d) :
    ∃ b : Basis (Fin 3) ℝ Space, (b : Fin 3 → Space) = p := by
  let independent := linearIndependent_unitChordTriangle_of_level p unit different n nonzero level
  have card : Fintype.card (Fin 3) = Module.finrank ℝ Space :=
    (finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin 3)).symm
  exact ⟨basisOfLinearIndependentOfCardEqFinrank independent card,
    coe_basisOfLinearIndependentOfCardEqFinrank _ _⟩

end Unfoldings
