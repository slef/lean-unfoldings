module

public import Unfoldings.Cone.SectorCoordinates

/-! The frontier of a closed sector consists exactly of its two actual closed rays. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

theorem frontier_planarSector (angle : ℝ) (nonzero : Real.sin angle ≠ 0) :
    frontier (planarSector angle) =
      Set.range (fun r : ℝ≥0 => (r : ℂ)) ∪
        Set.range (fun r : ℝ≥0 => polarRay angle * (r : ℂ)) := by
  let H := sectorCombinationHomeomorph angle nonzero
  have image : H '' (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) = planarSector angle :=
    sectorCombination_image_quadrant angle
  rw [← image, ← H.image_frontier, frontier_prod_eq, closure_Ici, frontier_Ici,
    Set.image_union]
  congr 1
  · ext z
    constructor
    · rintro ⟨⟨c, d⟩, ⟨hc, hd⟩, equal⟩
      have zero : d = 0 := Set.mem_singleton_iff.mp hd
      subst d
      change (c : ℂ) + (0 : ℝ) • polarRay angle = z at equal
      refine ⟨NNReal.mk c hc, ?_⟩
      change (c : ℂ) = z
      simpa only [zero_smul, add_zero] using equal
    · rintro ⟨r, rfl⟩
      refine ⟨((r : ℝ), 0), ⟨r.coe_nonneg, rfl⟩, ?_⟩
      change (r : ℂ) + (0 : ℝ) • polarRay angle = (r : ℂ)
      simp
  · ext z
    constructor
    · rintro ⟨⟨c, d⟩, ⟨hc, hd⟩, equal⟩
      have zero : c = 0 := Set.mem_singleton_iff.mp hc
      subst c
      change (0 : ℂ) + d • polarRay angle = z at equal
      refine ⟨NNReal.mk d hd, ?_⟩
      change polarRay angle * (d : ℂ) = z
      simpa only [zero_add, Complex.real_smul, mul_comm] using equal
    · rintro ⟨r, rfl⟩
      refine ⟨(0, (r : ℝ)), ⟨rfl, r.coe_nonneg⟩, ?_⟩
      change (0 : ℂ) + (r : ℝ) • polarRay angle = polarRay angle * (r : ℂ)
      simp [Complex.real_smul, mul_comm]

end Unfoldings
