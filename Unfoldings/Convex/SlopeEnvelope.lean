module

public import Unfoldings.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Order.Compact

/-! Compact-slope Legendre envelopes, with actual maximizers and supporting inequalities. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- A continuous dual cost restricted to a nonempty compact set of slopes. -/
structure SlopeEnvelope where
  slopes : Set Plane
  compact : IsCompact slopes
  nonempty : slopes.Nonempty
  dual : Plane → ℝ
  continuous_dual : Continuous dual

namespace SlopeEnvelope

variable (E : SlopeEnvelope)

/-- The affine function contributed by a slope. -/
def affine (p x : Plane) : ℝ := inner ℝ x p - E.dual p

/-- The clipped conjugate, defined on the entire plane. -/
def height (x : Plane) : ℝ := sSup ((fun p => E.affine p x) '' E.slopes)

theorem continuous_affine_slope (x : Plane) : Continuous (fun p => E.affine p x) :=
  (continuous_const.inner continuous_id).sub E.continuous_dual

theorem affine_le (x : Plane) {p : Plane} (member : p ∈ E.slopes) :
    E.affine p x ≤ E.height x :=
  le_csSup (E.compact.image (E.continuous_affine_slope x)).bddAbove ⟨p, member, rfl⟩

theorem exists_height_eq (x : Plane) : ∃ p ∈ E.slopes, E.height x = E.affine p x :=
  E.compact.exists_sSup_image_eq E.nonempty (E.continuous_affine_slope x).continuousOn

theorem height_le {x : Plane} {c : ℝ} (bound : ∀ p ∈ E.slopes, E.affine p x ≤ c) :
    E.height x ≤ c :=
  csSup_le (E.nonempty.image _) (by rintro _ ⟨p, hp, rfl⟩; exact bound p hp)

theorem continuous_height : Continuous E.height := by
  apply E.compact.continuous_sSup
  exact (continuous_fst.inner continuous_snd).sub (E.continuous_dual.comp continuous_snd)

/-- Active slopes are actual maximizing slopes, not supplied subgradient certificates. -/
def Active (x p : Plane) : Prop := p ∈ E.slopes ∧ E.height x = E.affine p x

theorem exists_active (x : Plane) : ∃ p, E.Active x p := by
  obtain ⟨p, hp, equal⟩ := E.exists_height_eq x
  exact ⟨p, hp, equal⟩

theorem active_iff {x p : Plane} (member : p ∈ E.slopes) :
    E.Active x p ↔ ∀ q ∈ E.slopes, E.affine q x ≤ E.affine p x := by
  constructor
  · rintro ⟨_, equal⟩ q hq
    exact equal ▸ E.affine_le x hq
  · intro bound
    exact ⟨member, le_antisymm (E.height_le bound) (E.affine_le x member)⟩

/-- One active slope controls every earlier point, including every incoming merger history. -/
theorem active_support {x p : Plane} (active : E.Active x p) (y : Plane) :
    E.height x - E.height y ≤ inner ℝ p (x - y) := by
  have bound := E.affine_le y active.1
  rw [active.2]
  have sx : inner ℝ p x = inner ℝ x p := real_inner_comm _ _
  have sy : inner ℝ p y = inner ℝ y p := real_inner_comm _ _
  dsimp [affine] at bound ⊢
  rw [inner_sub_right, sx, sy]
  linarith

theorem convex_height : ConvexOn ℝ Set.univ E.height := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb total
  obtain ⟨p, hp, equal⟩ := E.exists_height_eq (a • x + b • y)
  rw [equal]
  have hx := E.affine_le x hp
  have hy := E.affine_le y hp
  dsimp [affine] at hx hy ⊢
  simp only [inner_add_left, real_inner_smul_left]
  have balance := congrArg (fun c : ℝ => c * E.dual p) total
  simp only [add_mul, one_mul] at balance
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hx), mul_nonneg hb (sub_nonneg.mpr hy)]

end SlopeEnvelope
end Unfoldings
