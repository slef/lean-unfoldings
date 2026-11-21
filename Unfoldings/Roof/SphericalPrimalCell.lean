module

public import Unfoldings.Roof.Fenchel
public import Unfoldings.Cap.Gnomonic

/-! At every actual roof point, slope normal cells are the gnomonic coordinates
of the upward unit supporting directions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem slope_mem_primalNormalCell_iff_supports {z n : Space}
    (on_roof : z ∈ K.folding.surface) (up : 0 < n 2) :
    (n 2)⁻¹ • Cap.horizontal n ∈ K.primalNormalCell (Cap.horizontal z) ↔
      ∀ w ∈ K.folding.surface, inner ℝ n w ≤ inner ℝ n z := by
  let p := (n 2)⁻¹ • Cap.horizontal n
  have dot (w : Space) : inner ℝ n w =
      n 2 * (inner ℝ (Cap.horizontal w) p + w 2) := by
    rw [Cap.horizontal_inner]
    dsimp [p]
    rw [real_inner_smul_right, real_inner_comm (Cap.horizontal w) (Cap.horizontal n)]
    field_simp [up.ne']
  have at_z := (K.surface_iff_roofHeight z).mp on_roof
  constructor
  · intro support w hw
    have at_w := (K.surface_iff_roofHeight w).mp hw
    have test := support _ at_w.1
    rw [← at_w.2, ← at_z.2] at test
    rw [dot w, dot z]
    exact mul_le_mul_of_nonneg_left (by linarith only [test]) up.le
  · intro support x hx
    obtain ⟨w, hw, rfl⟩ := hx
    have at_w := (K.surface_iff_roofHeight w).mp hw
    have test := support w hw
    rw [dot w, dot z] at test
    have bound := le_of_mul_le_mul_left test up
    change inner ℝ (Cap.horizontal w) p - inner ℝ (Cap.horizontal z) p ≤
      -K.roofHeight (Cap.horizontal w) + K.roofHeight (Cap.horizontal z)
    rw [← at_w.2, ← at_z.2]
    linarith only [bound]

/-- The exact upward spatial normals at a point are the spherical image
of the full primal normal cell. -/
theorem gnomonicImage_primalNormalCell {z : Space} (on_roof : z ∈ K.folding.surface) :
    Cap.gnomonicNormal '' K.primalNormalCell (Cap.horizontal z) =
      {n : Space | ‖n‖ = 1 ∧ 0 < n 2 ∧
        ∀ w ∈ K.folding.surface, inner ℝ n w ≤ inner ℝ n z} := by
  ext n
  constructor
  · rintro ⟨p, support, rfl⟩
    have up := Cap.gnomonicNormal_upward p
    refine ⟨Cap.gnomonicNormal_unit p, up,
      (K.slope_mem_primalNormalCell_iff_supports on_roof up).mp ?_⟩
    rwa [Cap.slope_gnomonicNormal]
  · rintro ⟨unit, up, support⟩
    exact ⟨(n 2)⁻¹ • Cap.horizontal n, (K.slope_mem_primalNormalCell_iff_supports on_roof up).mpr
      support, Cap.gnomonicNormal_slope n unit up⟩

end Unfoldings.ConvexRoof
