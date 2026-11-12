module

public import Unfoldings.Path.Subpath
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.IntermediateValue

/-! Stop a continuous path at its first intersection with a source sphere. -/

@[expose] public section

namespace Unfoldings

variable {X : Type*} [PseudoMetricSpace X] {a b : X}

/-- A first sphere intersection exists without radial monotonicity. Every earlier
point is strictly inside the ball, which is needed before appending an exterior arc. -/
theorem exists_first_path_radius (P : Path a b) (source : X) (radius : ℝ)
    (start : dist source a < radius) (finish : radius ≤ dist source b) :
    ∃ t : unitInterval, 0 < t ∧ dist source (P t) = radius ∧
      ∀ s : unitInterval, s < t → dist source (P s) < radius := by
  let f := fun s : unitInterval => dist source (P s)
  have continuous : Continuous f := continuous_const.dist P.continuous
  have first : f 0 < radius := by
    change dist source (P 0) < radius
    rw [P.source]
    exact start
  have last : radius ≤ f 1 := by
    change radius ≤ dist source (P 1)
    rw [P.target]
    exact finish
  obtain ⟨u, _, equal⟩ := intermediate_value_Icc (show (0 : unitInterval) ≤ 1 from zero_le_one)
    continuous.continuousOn ⟨first.le, last⟩
  have compact : IsCompact {s : unitInterval | f s = radius} :=
    (isClosed_eq continuous continuous_const).isCompact
  obtain ⟨t, least⟩ := compact.exists_isLeast ⟨u, equal⟩
  have positive : (0 : unitInterval) < t := by
    by_contra not_positive
    have zero : t = 0 := le_antisymm (le_of_not_gt not_positive) t.property.1
    have at_t := least.1
    change f t = radius at at_t
    rw [zero] at at_t
    linarith
  refine ⟨t, positive, least.1, ?_⟩
  intro s earlier
  by_contra not_inside
  have outside : radius ≤ f s := le_of_not_gt not_inside
  obtain ⟨v, bounds, at_v⟩ := intermediate_value_Icc
    (show (0 : unitInterval) ≤ s from s.property.1) continuous.continuousOn ⟨first.le, outside⟩
  have lower : t ≤ v := least.2 at_v
  exact (not_le_of_gt earlier) (lower.trans bounds.2)

/-- The affine subpath to that first crossing has every nonterminal point strictly
inside the ball. The path may have repeated points; simplicity is a separate property. -/
theorem exists_initial_subpath_to_sphere (P : Path a b) (source : X) (radius : ℝ)
    (start : dist source a < radius) (finish : radius ≤ dist source b) :
    ∃ t : unitInterval, 0 < t ∧ dist source (P t) = radius ∧
      ∀ s : unitInterval, s < 1 → dist source (P.subpath 0 t s) < radius := by
  obtain ⟨t, positive, at_t, earlier⟩ := exists_first_path_radius P source radius start finish
  refine ⟨t, positive, at_t, fun s before => earlier _ ?_⟩
  change AffineMap.lineMap (0 : ℝ) (t : ℝ) (s : ℝ) < (t : ℝ)
  rw [AffineMap.lineMap_apply_module]
  simp only [smul_eq_mul, mul_zero, zero_add]
  change (0 : ℝ) < (t : ℝ) at positive
  change (s : ℝ) < 1 at before
  nlinarith

theorem initial_subpath_injective (P : Path a b) (injective : Function.Injective P)
    (t : unitInterval) (positive : 0 < t) : Function.Injective (P.subpath 0 t) := by
  intro s r equal
  have parameters : Path.intervalParam 0 t s = Path.intervalParam 0 t r := injective equal
  apply Subtype.ext
  exact AffineMap.lineMap_injective ℝ (show (0 : ℝ) ≠ (t : ℝ) from ne_of_lt positive)
    (congrArg Subtype.val parameters)

/-- A simple path remains simple when stopped at its first sphere crossing. -/
theorem exists_injective_initial_subpath_to_sphere (P : Path a b)
    (injective : Function.Injective P) (source : X) (radius : ℝ)
    (start : dist source a < radius) (finish : radius ≤ dist source b) :
    ∃ t : unitInterval, 0 < t ∧ dist source (P t) = radius ∧
      Function.Injective (P.subpath 0 t) ∧
      ∀ s : unitInterval, s < 1 → dist source (P.subpath 0 t s) < radius := by
  obtain ⟨t, positive, equal, inside⟩ :=
    exists_initial_subpath_to_sphere P source radius start finish
  exact ⟨t, positive, equal, initial_subpath_injective P injective t positive, inside⟩

end Unfoldings
