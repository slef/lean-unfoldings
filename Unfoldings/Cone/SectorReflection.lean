module

public import Unfoldings.Cone.SectorCoordinates
public import Mathlib.Analysis.Complex.Isometry

/-!
# Reversing the two boundary rays of a sector

Reflection in the angular bisector is an actual linear isometry. It preserves
the closed sector and exchanges its unit boundary vectors. This permits the
orientation of each ordered corner to follow its chosen initial link germ.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

def sectorFlip (α : ℝ) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  Complex.conjLIE.trans (rotation (Circle.exp α))

theorem sectorFlip_apply (α : ℝ) (z : ℂ) :
    sectorFlip α z = polarRay α * starRingEnd ℂ z := rfl

@[simp] theorem polarRay_mul_conj (α : ℝ) :
    polarRay α * starRingEnd ℂ (polarRay α) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_polarRay]
  norm_num

@[simp] theorem sectorFlip_one (α : ℝ) : sectorFlip α 1 = polarRay α := by
  simp [sectorFlip_apply]

@[simp] theorem sectorFlip_ray (α : ℝ) : sectorFlip α (polarRay α) = 1 := by
  exact polarRay_mul_conj α

theorem sectorFlip_involutive (α : ℝ) : Function.Involutive (sectorFlip α) := by
  intro z
  rw [sectorFlip_apply, sectorFlip_apply, map_mul, Complex.conj_conj,
    ← mul_assoc, polarRay_mul_conj, one_mul]

theorem sectorFlip_mem (α : ℝ) {z : ℂ} (inside : z ∈ planarSector α) :
    sectorFlip α z ∈ planarSector α := by
  obtain ⟨c, hc, d, hd, rfl⟩ := inside
  refine ⟨d, hd, c, hc, ?_⟩
  have cast_c : (c : ℂ) = c • (1 : ℂ) := by simp [Complex.real_smul]
  rw [cast_c, map_add, map_smul, map_smul, sectorFlip_one, sectorFlip_ray]
  simp [Complex.real_smul, add_comm]

/-- Reflection exchanges the banks while preserving the actual sector metric. -/
def sectorFlipIsometry (α : ℝ) : planarSector α ≃ᵢ planarSector α where
  toFun x := ⟨sectorFlip α x.val, sectorFlip_mem α x.property⟩
  invFun x := ⟨sectorFlip α x.val, sectorFlip_mem α x.property⟩
  left_inv x := Subtype.ext (sectorFlip_involutive α x.val)
  right_inv x := Subtype.ext (sectorFlip_involutive α x.val)
  isometry_toFun x y := (sectorFlip α).isometry x.val y.val

@[simp] theorem sectorFlipIsometry_apply (α : ℝ) (x : planarSector α) :
    (sectorFlipIsometry α x).val = sectorFlip α x.val := rfl

end Unfoldings
