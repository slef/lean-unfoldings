module

public import Unfoldings.Convex.HistoryCone

/-! Forward growth of a compact support envelope is realized at an active slope. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope

variable (E : SlopeEnvelope)

/-- If every positive partial step has a uniform gain, a slope attaining
the envelope at the initial point realizes that forward gain. -/
theorem exists_active_of_forward_gain (x d : Plane) {gain : ℝ}
    (progress : ∀ t : ℝ, 0 < t → t * gain ≤ E.height (x + t • d) - E.height x) :
    ∃ p, E.Active x p ∧ gain ≤ inner ℝ p d := by
  let S := E.slopes ∩ {p | gain ≤ inner ℝ p d}
  have compact : IsCompact S := E.compact.inter_right
    (isClosed_le continuous_const (continuous_id.inner continuous_const))
  let ray (t : ℝ) := x + t • d
  have affine (p : Plane) (t : ℝ) : E.affine p (ray t) = E.affine p x + t * inner ℝ p d := by
    simp only [SlopeEnvelope.affine, ray]
    rw [inner_add_left, real_inner_smul_left, real_inner_comm p d]
    ring
  have active_in_S (t : ℝ) (positive : 0 < t) :
      ∃ p ∈ S, E.height (ray t) = E.affine p (ray t) := by
    obtain ⟨p, member, hp⟩ := E.exists_height_eq (ray t)
    have lower := progress t positive
    change t * gain ≤ E.height (ray t) - E.height x at lower
    have upper := E.affine_le x member
    rw [hp, affine] at lower
    have h : t * gain ≤ t * inner ℝ p d := by linarith only [lower, upper]
    exact ⟨p, ⟨member, (mul_le_mul_iff_of_pos_left positive).mp h⟩, hp⟩
  have nonempty : S.Nonempty := by
    obtain ⟨p, member, _⟩ := active_in_S 1 zero_lt_one
    exact ⟨p, member⟩
  let restricted : SlopeEnvelope := ⟨S, compact, nonempty, E.dual, E.continuous_dual⟩
  have equals (t : ℝ) (positive : 0 < t) : restricted.height (ray t) = E.height (ray t) := by
    obtain ⟨p, member, hp⟩ := active_in_S t positive
    refine le_antisymm (restricted.height_le (fun _ h => E.affine_le _ h.1)) ?_
    rw [hp]
    exact restricted.affine_le _ member
  have continuous_ray : Continuous ray := continuous_const.add (continuous_id.smul continuous_const)
  have closed : IsClosed {t | restricted.height (ray t) = E.height (ray t)} := isClosed_eq
    (restricted.continuous_height.comp continuous_ray) (E.continuous_height.comp continuous_ray)
  have at_zero : 0 ∈ closure (Set.Ioi (0 : ℝ)) := by rw [closure_Ioi]; exact le_rfl
  have same := closure_minimal (show Set.Ioi (0 : ℝ) ⊆ {t |
    restricted.height (ray t) = E.height (ray t)} from fun _ h => equals _ h) closed at_zero
  have equal : restricted.height x = E.height x := by
    change restricted.height (ray 0) = E.height (ray 0) at same
    simpa only [ray, zero_smul, add_zero] using same
  obtain ⟨p, member, at_x⟩ := restricted.exists_height_eq x
  exact ⟨p, ⟨member.1, equal.symm.trans at_x⟩, member.2⟩

end Unfoldings.SlopeEnvelope
