module

public import Unfoldings.Geometry.DirectionWedgeOperations

/-! Linear coordinate margins and source-centered direction wedges persist on whole chords. -/

@[expose] public section

namespace Unfoldings

section LinearCoordinates

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem lineMap_frame_sub_quadrant_lower_bound (frame : E →ₗ[ℝ] ℂ)
    (source x y : E) (lower : ℝ) {s : ℝ} (parameter : s ∈ Set.Icc 0 1)
    (first : lower ≤ (frame (x - source)).re ∧ lower ≤ (frame (x - source)).im)
    (last : lower ≤ (frame (y - source)).re ∧ lower ≤ (frame (y - source)).im) :
    lower ≤ (frame (AffineMap.lineMap x y s - source)).re ∧
      lower ≤ (frame (AffineMap.lineMap x y s - source)).im := by
  have displacement : AffineMap.lineMap x y s - source =
      (1 - s) • (x - source) + s • (y - source) := by
    rw [AffineMap.lineMap_apply_module]
    module
  rw [displacement, map_add, map_smul, map_smul]
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  constructor <;> nlinarith [parameter.1, parameter.2]

end LinearCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u v source x y p : E}

theorem InDirectionWedge.sub_of_mem_segment
    (first : InDirectionWedge u v (x - source)) (last : InDirectionWedge u v (y - source))
    (member : p ∈ segment ℝ x y) : InDirectionWedge u v (p - source) := by
  have convex : Convex ℝ {p : E | InDirectionWedge u v (p - source)} :=
    (convex_inDirectionWedge u v).affine_preimage
      (AffineMap.id ℝ E - AffineMap.const ℝ E source)
  exact convex.segment_subset first last member

end Unfoldings
