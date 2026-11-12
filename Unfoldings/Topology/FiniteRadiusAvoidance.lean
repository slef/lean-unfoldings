module

public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Topology.Sets.Opens

/-! Open overlap is detected on a source circle outside any finite exceptional radius set. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

theorem dense_avoiding_finite_radii (center : E) {exception : Set ℝ}
    (finite : exception.Finite) : Dense {z : E | ‖z - center‖ ∉ exception} := by
  let := finite.to_subtype
  let D := fun r : exception => (Metric.sphere center r.val)ᶜ
  have opened (r : exception) : IsOpen (D r) := Metric.isClosed_sphere.isOpen_compl
  have dense (r : exception) : Dense (D r) :=
    interior_eq_empty_iff_dense_compl.mp (interior_sphere' center r.val)
  have all_dense := (Set.finite_range D).dense_sInter
    (by rintro U ⟨r, rfl⟩; exact opened r)
    (by rintro U ⟨r, rfl⟩; exact dense r)
  have equal : ⋂₀ Set.range D = {z : E | ‖z - center‖ ∉ exception} := by
    ext z
    constructor
    · intro member inside
      have avoid := member (D ⟨‖z - center‖, inside⟩) ⟨⟨‖z - center‖, inside⟩, rfl⟩
      exact avoid (by rw [Metric.mem_sphere, dist_eq_norm])
    · intro avoid U in_family
      obtain ⟨r, rfl⟩ := in_family
      intro on_sphere
      have size : ‖z - center‖ = r.val := by
        simpa only [Metric.mem_sphere, dist_eq_norm] using on_sphere
      exact avoid (size.symm ▸ r.property)
  exact equal ▸ all_dense

/-- Finite exceptional circles cannot hide an intersection of two open developed regions. -/
theorem disjoint_open_of_circle_disjoint_off_finite {U V : Set E}
    (first : IsOpen U) (last : IsOpen V) (center : E) {exception : Set ℝ}
    (finite : exception.Finite)
    (separated : ∀ radius ∉ exception,
      Disjoint (U ∩ {z | ‖z - center‖ = radius}) (V ∩ {z | ‖z - center‖ = radius})) :
    Disjoint U V := by
  apply Set.disjoint_left.mpr
  intro z in_first in_last
  have dense := dense_avoiding_finite_radii center finite
  obtain ⟨p, ⟨p_first, p_last⟩, avoid⟩ :=
    dense.inter_open_nonempty (U ∩ V) (first.inter last) ⟨z, in_first, in_last⟩
  exact Set.disjoint_left.mp (separated ‖p - center‖ avoid) ⟨p_first, rfl⟩ ⟨p_last, rfl⟩

/-- Only the positive circles below the controlled radius are needed to rule
out open overlap inside that radius. The center adds one harmless exception. -/
theorem disjoint_open_in_ball_of_circle_disjoint_off_finite {U V : Set E}
    (first : IsOpen U) (last : IsOpen V) (center : E) (bound : ℝ) {exception : Set ℝ}
    (finite : exception.Finite)
    (separated : ∀ radius ∈ Set.Ioo (0 : ℝ) bound, radius ∉ exception →
      Disjoint (U ∩ {z | ‖z - center‖ = radius}) (V ∩ {z | ‖z - center‖ = radius})) :
    Disjoint (U ∩ Metric.ball center bound) (V ∩ Metric.ball center bound) := by
  apply Set.disjoint_left.mpr
  intro z first_member last_member
  have dense := dense_avoiding_finite_radii center (finite.insert 0)
  obtain ⟨p, ⟨p_first, p_last⟩, avoid⟩ := dense.inter_open_nonempty
    ((U ∩ Metric.ball center bound) ∩ (V ∩ Metric.ball center bound))
    ((first.inter Metric.isOpen_ball).inter (last.inter Metric.isOpen_ball))
    ⟨z, first_member, last_member⟩
  have nonzero : ‖p - center‖ ≠ 0 := fun equal => avoid (Or.inl equal)
  have before : ‖p - center‖ < bound := by
    simpa only [Metric.mem_ball, dist_eq_norm] using p_first.2
  exact Set.disjoint_left.mp (separated ‖p - center‖
    ⟨lt_of_le_of_ne (norm_nonneg _) (Ne.symm nonzero), before⟩
    (fun member => avoid (Or.inr member))) ⟨p_first.1, rfl⟩ ⟨p_last.1, rfl⟩

end Unfoldings
