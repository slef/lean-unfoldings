module

public import Unfoldings.Convex.CoerciveEnvelope
public import Unfoldings.Convex.ExteriorPlan

/-! Translate the slope reference for coercivity and ray truncation while retaining
the original planar coordinates and physical roof heights. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope

variable (E : SlopeEnvelope) (reference : Plane)

/-- Subtract the same slope from every support plane. The maximizing supports
and all projected edges stay in their original horizontal coordinates. -/
def recenter : SlopeEnvelope where
  slopes := (fun p => p - reference) '' E.slopes
  compact := E.compact.image (continuous_id.sub continuous_const)
  nonempty := E.nonempty.image _
  dual p := E.dual (p + reference)
  continuous_dual := E.continuous_dual.comp (continuous_id.add continuous_const)

@[simp] theorem mem_recenter_slopes {p : Plane} :
    p ∈ (E.recenter reference).slopes ↔ p + reference ∈ E.slopes := by
  constructor
  · rintro ⟨q, member, rfl⟩
    simpa only [sub_add_cancel] using member
  · intro member
    exact ⟨p + reference, member, add_sub_cancel_right _ _⟩

@[simp] theorem recenter_affine (p x : Plane) :
    (E.recenter reference).affine (p - reference) x =
      E.affine p x - inner ℝ x reference := by
  change inner ℝ x (p - reference) - E.dual (p - reference + reference) =
    inner ℝ x p - E.dual p - inner ℝ x reference
  rw [inner_sub_right, sub_add_cancel]
  ring

/-- The recentered potential differs from physical height by a fixed linear functional. -/
theorem recenter_height (x : Plane) :
    (E.recenter reference).height x = E.height x - inner ℝ x reference := by
  apply le_antisymm
  · apply (E.recenter reference).height_le
    rintro _ ⟨p, member, rfl⟩
    rw [E.recenter_affine]
    exact sub_le_sub_right (E.affine_le x member) _
  · obtain ⟨p, member, realizes⟩ := E.exists_height_eq x
    rw [realizes, ← E.recenter_affine]
    exact (E.recenter reference).affine_le x ⟨p, member, rfl⟩

theorem recenter_active_iff {p x : Plane} :
    (E.recenter reference).Active x (p - reference) ↔ E.Active x p := by
  simp only [Active, E.mem_recenter_slopes, sub_add_cancel, E.recenter_height, E.recenter_affine,
    sub_left_inj]

/-- A support direction keeps the same exposed slopes after translation. -/
theorem recenter_support {p d : Plane}
    (supports : ∀ q ∈ E.slopes, inner ℝ d q ≤ inner ℝ d p) :
    ∀ q ∈ (E.recenter reference).slopes, inner ℝ d q ≤ inner ℝ d (p - reference) := by
  rintro _ ⟨q, member, rfl⟩
  simpa only [inner_sub_right, sub_le_sub_iff_right] using supports q member

theorem original_support_of_recenter {p d : Plane}
    (supports : ∀ q ∈ (E.recenter reference).slopes, inner ℝ d q ≤ inner ℝ d p) :
    ∀ q ∈ E.slopes, inner ℝ d q ≤ inner ℝ d (p + reference) := by
  intro q member
  have bound := supports (q - reference) ⟨q, member, rfl⟩
  rw [inner_sub_right] at bound
  rw [inner_add_right]
  linarith only [bound]

/-- Any interior slope gives a compact exhaustion by affine sections. -/
theorem compact_recenter_sublevel (inside : reference ∈ interior E.slopes) (level : ℝ) :
    IsCompact {x | (E.recenter reference).height x ≤ level} := by
  obtain ⟨a, positive, contained⟩ :=
    Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp inside)
  apply (E.recenter reference).compact_sublevel positive
  intro p member
  apply (E.mem_recenter_slopes reference).mpr
  apply contained
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]
  simpa only [Metric.mem_ball, dist_zero_right] using member

end Unfoldings.SlopeEnvelope
