module

public import Unfoldings.Roof.TentCompletion

/-! Properness and arbitrarily deep compact clips of completed arbitrary-rim roofs. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- The Euclidean norm is bounded by the sum of the absolute planar coordinates. -/
theorem plane_norm_le_sum_abs (p : Plane) : ‖p‖ ≤ |p 0| + |p 1| := by
  have squared := EuclideanSpace.real_norm_sq_eq p
  rw [Fin.sum_univ_two] at squared
  nlinarith [norm_nonneg p, abs_nonneg (p 0), abs_nonneg (p 1),
    sq_abs (p 0), sq_abs (p 1), mul_nonneg (abs_nonneg (p 0)) (abs_nonneg (p 1))]

namespace ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem continuous_tentCompletionHeight (H L : ℝ) : Continuous (K.tentCompletionHeight H L) :=
  AffineEnvelope.continuous_height (K.tentCompletionSupport H L)

theorem tentCompletionHeight_coercive (H : ℝ) {L : ℝ} (nonnegative : 0 ≤ L) (p : Plane) :
    K.tentCompletionHeight H L p ≤ H - L * ‖p‖ :=
  (K.tentCompletionHeight_le_tent H L p).trans
    (sub_le_sub_left (mul_le_mul_of_nonneg_left (plane_norm_le_sum_abs p) nonnegative) H)

/-- Positive tent slope makes every finite horizontal clip compact, for arbitrary rim heights. -/
theorem isCompact_tentCompletionClip (H : ℝ) {L : ℝ} (positive : 0 < L) (Z : ℝ) :
    IsCompact (K.tentCompletionClip H L Z) := by
  apply (isCompact_closedBall (0 : Plane) ((H - Z) / L)).of_isClosed_subset
    (AffineEnvelope.isClosed_clip (K.tentCompletionSupport H L) Z)
  intro p member
  rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ positive]
  have upper := K.tentCompletionHeight_coercive H positive.le p
  change Z ≤ K.tentCompletionHeight H L p at member
  linarith

/-- The clipping frontier lies in its actual prescribed horizontal plane. -/
theorem tentCompletionHeight_eq_level_of_frontier (H L Z : ℝ) {p : Plane}
    (boundary : p ∈ frontier (K.tentCompletionClip H L Z)) :
    K.tentCompletionHeight H L p = Z :=
  AffineEnvelope.height_eq_level_of_frontier (K.tentCompletionSupport H L) boundary

/-- A sufficiently low horizontal clip contains any prescribed compact region strictly
inside its footprint. The choice precedes auxiliary triangulation. -/
theorem exists_deep_tentCompletionClip (H L Z₀ : ℝ) {S : Set Plane} (compact : IsCompact S) :
    ∃ Z < Z₀, S ⊆ interior (K.tentCompletionClip H L Z) := by
  obtain ⟨b, bound⟩ := compact.bddBelow_image (K.continuous_tentCompletionHeight H L).continuousOn
  refine ⟨min b Z₀ - 1, by linarith [min_le_right b Z₀], ?_⟩
  intro p member
  apply AffineEnvelope.mem_interior_clip (K.tentCompletionSupport H L)
  change min b Z₀ - 1 < K.tentCompletionHeight H L p
  have lower : b ≤ K.tentCompletionHeight H L p := bound ⟨p, member, rfl⟩
  linarith [min_le_left b Z₀]

/-- The tent can be made inactive on every original whole face while its lower compact
sections contain the entire original domain in their interior. -/
theorem exists_proper_tent_completion {L : ℝ} (positive : 0 < L) :
    ∃ H : ℝ,
      (∀ p ∈ K.footprint, K.tentCompletionHeight H L p = K.roofHeight p) ∧
      (∀ Z : ℝ, IsCompact (K.tentCompletionClip H L Z)) ∧
      (∀ Z₀ : ℝ, ∃ Z < Z₀, K.footprint ⊆ interior (K.tentCompletionClip H L Z)) := by
  obtain ⟨H, inactive⟩ := K.exists_tent_height L
  exact ⟨H, fun _ member => K.tentCompletionHeight_eq_on_footprint positive.le inactive member,
    K.isCompact_tentCompletionClip H positive,
    fun Z₀ => K.exists_deep_tentCompletionClip H L Z₀ K.compact_footprint⟩

end ConvexRoof
end Unfoldings
