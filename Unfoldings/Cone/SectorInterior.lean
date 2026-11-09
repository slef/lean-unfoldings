module

public import Unfoldings.Cone.SectorCoordinates

/-!
# Genuine interiors in polar sector coordinates

A sector of angle strictly between zero and pi has interior exactly at
positive radii and strictly intermediate real headings.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem exists_polar_of_mem_interior_planarSector (α : ℝ)
    (positive : 0 < α) (small : α < Real.pi)
    (z : ℂ) (inside : z ∈ interior (planarSector α)) :
    ∃ r : ℝ, 0 < r ∧ ∃ θ ∈ Set.Ioo 0 α, z = (r : ℂ) * polarRay θ := by
  have sine : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi positive small
  have closed_inside := interior_subset inside
  rw [interior_planarSector α sine.ne'] at inside
  obtain ⟨c, hc, d, hd, coordinates⟩ := inside
  have imaginary : 0 < z.im := by
    rw [coordinates]
    simpa [Complex.real_smul] using mul_pos hd sine
  have nonzero : z ≠ 0 := by
    intro zero
    rw [zero, Complex.zero_im] at imaginary
    exact lt_irrefl 0 imaginary
  obtain ⟨r, rpos, θ, bounds, polar⟩ := exists_polar_of_mem_planarSector α positive small z
    closed_inside nonzero
  have initial : θ ≠ 0 := by
    intro zero
    have original : sectorCombination α (c, d) = z := coordinates.symm
    have boundary : sectorCombination α (r, 0) = z := by
      simp only [sectorCombination, zero_smul, add_zero]
      rw [polar, zero, polarRay_zero, mul_one]
    have pairs := (sectorCombinationHomeomorph α sine.ne').injective
      (original.trans boundary.symm)
    exact hd.ne' (congrArg Prod.snd pairs)
  have terminal : θ ≠ α := by
    intro last
    have original : sectorCombination α (c, d) = z := coordinates.symm
    have boundary : sectorCombination α (0, r) = z := by
      simp only [sectorCombination, Complex.ofReal_zero, zero_add, Complex.real_smul]
      rw [polar, last]
    have pairs := (sectorCombinationHomeomorph α sine.ne').injective
      (original.trans boundary.symm)
    exact hc.ne' (congrArg Prod.fst pairs)
  exact ⟨r, rpos, θ,
    ⟨lt_of_le_of_ne bounds.1 initial.symm, lt_of_le_of_ne bounds.2 terminal⟩, polar⟩

theorem polar_mem_interior_planarSector (α r θ : ℝ) (positive : 0 < α)
    (small : α < Real.pi) (radius : 0 < r) (heading : θ ∈ Set.Ioo 0 α) :
    (r : ℂ) * polarRay θ ∈ interior (planarSector α) := by
  have sine : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi positive small
  obtain ⟨c, hc, d, hd, combination⟩ := polarRay_mem_strict_positive_span 0 α θ
    (by simpa only [sub_zero] using small) heading
  rw [interior_planarSector α sine.ne']
  refine ⟨r * c, mul_pos radius hc, r * d, mul_pos radius hd, ?_⟩
  rw [combination, polarRay_zero]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring

theorem mem_interior_planarSector_iff_polar (α : ℝ) (positive : 0 < α)
    (small : α < Real.pi) (z : ℂ) :
    z ∈ interior (planarSector α) ↔
      ∃ r : ℝ, 0 < r ∧ ∃ θ ∈ Set.Ioo 0 α, z = (r : ℂ) * polarRay θ := by
  constructor
  · exact exists_polar_of_mem_interior_planarSector α positive small z
  · rintro ⟨r, radius, θ, heading, rfl⟩
    exact polar_mem_interior_planarSector α r θ positive small radius heading

end Unfoldings
