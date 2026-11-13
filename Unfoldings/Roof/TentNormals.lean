module

public import Unfoldings.Roof.TentClips
public import Unfoldings.Geometry.GraphNormal

/-! Adding four distant tent supports preserves a prescribed shallow tilt bound. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

/-- The actual negative gradient of each of the four added support planes. -/
def tentSlope (L : ℝ) (s : Bool × Bool) : Plane :=
  WithLp.toLp 2 ![if s.1 then L else -L, if s.2 then L else -L]

theorem tentSlope_norm_sq (L : ℝ) (s : Bool × Bool) : ‖tentSlope L s‖ ^ 2 = 2 * L ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rcases s with ⟨a, b⟩
  cases a <;> cases b <;> simp [tentSlope] <;> ring

theorem tentSupport_eq_inner (H L : ℝ) (s : Bool × Bool) (p : Plane) :
    tentSupport H L s p = H - inner ℝ (tentSlope L s) p := by
  rw [tentSupport_apply]
  rcases s with ⟨a, b⟩
  cases a <;> cases b <;>
    simp [tentSlope, PiLp.inner_apply, Fin.sum_univ_two] <;> ring

/-- Every point on the added affine graph lies in the claimed upward-normal plane. -/
theorem tentSupport_normal_height (H L : ℝ) (s : Bool × Bool) (p : Plane) :
    inner ℝ (graphNormal (tentSlope L s)) (Cap.horizontalAtHeight p (tentSupport H L s p)) =
      (Real.sqrt (1 + 2 * L ^ 2))⁻¹ * H := by
  rw [graphNormal_inner, Cap.horizontal_horizontalAtHeight, Cap.height_horizontalAtHeight,
    tentSupport_eq_inner, tentSlope_norm_sq]
  ring

/-- An arbitrarily shallow positive tent slope works for every old roof: its supports can
be moved upward before clipping. No loss in the chosen normal tilt budget is necessary. -/
theorem tentNormal_tilt {φ : ℝ} (positive : 0 < φ) (small : φ < Real.pi / 2)
    (s : Bool × Bool) :
    Real.cos φ ≤ graphNormal (tentSlope (Real.sin φ / 2) s) 2 := by
  have cos_positive : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], small⟩
  apply graphNormal_vertical_ge cos_positive.le
  rw [tentSlope_norm_sq]
  have identity := Real.sin_sq_add_cos_sq φ
  have c_bound : (Real.cos φ) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (Real.sin φ)]
  have product := mul_le_mul_of_nonneg_right c_bound (sq_nonneg (Real.sin φ))
  nlinarith

/-- The tent slope used by the completion is strictly positive whenever the tilt budget is. -/
theorem tent_slope_positive {φ : ℝ} (positive : 0 < φ) (small : φ < Real.pi / 2) :
    0 < Real.sin φ / 2 := by
  have sine := Real.sin_pos_of_pos_of_lt_pi positive (by linarith [Real.pi_pos])
  positivity

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Old supporting normals are unchanged; each added plane uses its actual graph normal. -/
def tentCompletionNormal (L : ℝ) : Face ⊕ (Bool × Bool) → Space :=
  Sum.elim K.normal (fun s => graphNormal (tentSlope L s))

theorem tentCompletionNormal_unit (L : ℝ) (i : Face ⊕ (Bool × Bool)) :
    ‖K.tentCompletionNormal L i‖ = 1 := by
  cases i with
  | inl f => exact K.normal_unit f
  | inr s => exact graphNormal_unit _

theorem tentCompletionNormal_upward (L : ℝ) (i : Face ⊕ (Bool × Bool)) :
    0 < K.tentCompletionNormal L i 2 := by
  cases i with
  | inl f => exact K.normal_upward f
  | inr s => exact graphNormal_upward _

/-- The completion preserves the entire prescribed normal tilt bound. -/
theorem tentCompletionNormal_tilt {φ : ℝ} (positive : 0 < φ) (small : φ < Real.pi / 2)
    (tilt : K.TiltBound φ) (i : Face ⊕ (Bool × Bool)) :
    Real.cos φ ≤ K.tentCompletionNormal (Real.sin φ / 2) i 2 := by
  cases i with
  | inl f => exact tilt f
  | inr s => exact tentNormal_tilt positive small s

/-- Every added plane and every old plane supports the entire completed graph. -/
theorem tentCompletionNormal_supporting (H L : ℝ) (i : Face ⊕ (Bool × Bool))
    (p q : Plane) (active : K.tentCompletionHeight H L p = K.tentCompletionSupport H L i p) :
    inner ℝ (K.tentCompletionNormal L i)
      (Cap.horizontalAtHeight q (K.tentCompletionHeight H L q) -
        Cap.horizontalAtHeight p (K.tentCompletionHeight H L p)) ≤ 0 := by
  have upper := AffineEnvelope.height_le (K.tentCompletionSupport H L) q i
  cases i with
  | inl f =>
    change K.tentCompletionHeight H L p = K.supportHeight f p at active
    change K.tentCompletionHeight H L q ≤ K.supportHeight f q at upper
    rw [K.supportHeight_apply, le_div_iff₀ (K.normal_upward f)] at upper
    rw [K.supportHeight_apply, eq_div_iff (K.normal_upward f).ne'] at active
    change inner ℝ (K.normal f) _ ≤ 0
    rw [inner_sub_right, Cap.horizontal_inner, Cap.horizontal_inner,
      Cap.horizontal_horizontalAtHeight, Cap.horizontal_horizontalAtHeight,
      Cap.height_horizontalAtHeight, Cap.height_horizontalAtHeight]
    linarith
  | inr s =>
    change K.tentCompletionHeight H L p = tentSupport H L s p at active
    change K.tentCompletionHeight H L q ≤ tentSupport H L s q at upper
    rw [tentSupport_eq_inner] at active upper
    change inner ℝ (graphNormal (tentSlope L s)) _ ≤ 0
    rw [inner_sub_right, graphNormal_inner, graphNormal_inner,
      Cap.horizontal_horizontalAtHeight, Cap.horizontal_horizontalAtHeight,
      Cap.height_horizontalAtHeight, Cap.height_horizontalAtHeight, ← mul_sub]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

end Unfoldings.ConvexRoof
