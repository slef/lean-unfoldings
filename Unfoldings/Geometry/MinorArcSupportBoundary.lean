module

public import Unfoldings.Geometry.MinorArcConnectivity
public import Mathlib.Data.Finset.Max

/-! A change of membership in a convex spherical selector crosses an actual support. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- A minor arc from the strict interior of a finite halfspace intersection
to its exterior has a first crossing on the actual supported boundary. -/
theorem exists_openMinorArc_support_boundary {I : Type*} [Finite I]
    (f : I → Space →ₗ[ℝ] ℝ) {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (not_antipodal : u + v ≠ 0) (inside : ∀ i, 0 < f i u) (outside : ¬ ∀ i, 0 ≤ f i v) :
    ∃ x ∈ openMinorArc u v, x ∈ Metric.sphere (0 : Space) 1 ∧
      (∀ i, 0 ≤ f i x) ∧ ∃ j, f j x = 0 := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let negative := Finset.univ.filter (fun i => f i v < 0)
  let time (i : I) := f i u / (f i u - f i v)
  have nonempty : negative.Nonempty := by
    push Not at outside
    obtain ⟨i, hi⟩ := outside
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have is_neg (i : I) (h : i ∈ negative) : f i v < 0 := (Finset.mem_filter.mp h).2
  have duration (i : I) (h : i ∈ negative) : 0 < f i u - f i v :=
    sub_pos.mpr ((is_neg i h).trans (inside i))
  obtain ⟨j, member, first⟩ := Finset.exists_min_image negative time nonempty
  let t := time j
  have t_pos : 0 < t := div_pos (inside j) (duration j member)
  have t_short : t < 1 := (div_lt_one (duration j member)).mpr (by linarith only [is_neg j member])
  let chord := (1 - t) • u + t • v
  have f_chord (i : I) : f i chord = (1 - t) * f i u + t * f i v := by
    simp only [chord, map_add, map_smul, smul_eq_mul]
  have support (i : I) : 0 ≤ f i chord := by
    rw [f_chord]
    by_cases below : f i v < 0
    · have marked : i ∈ negative := Finset.mem_filter.mpr ⟨Finset.mem_univ _, below⟩
      have before := (le_div_iff₀ (duration i marked)).mp (first i marked)
      linarith only [before]
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t_short.le) (inside i).le)
        (mul_nonneg t_pos.le (le_of_not_gt below))
  have equal : f j chord = 0 := by
    have exact_time : t * (f j u - f j v) = f j u := div_mul_cancel₀ _ (duration j member).ne'
    rw [f_chord]
    linarith only [exact_time]
  have arc : NormedSpace.normalize chord ∈ openMinorArc u v := ⟨t, ⟨t_pos, t_short⟩, rfl⟩
  have unit := closedMinorArc_subset_sphere hu hv not_antipodal
    (Set.mem_insert_of_mem u (Set.mem_insert_of_mem v arc))
  refine ⟨NormedSpace.normalize chord, arc, unit, ?_, j, ?_⟩
  · intro i
    rw [NormedSpace.normalize, map_smul, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (support i)
  · rw [NormedSpace.normalize, map_smul, equal, smul_zero]

/-- An open minor arc does not depend on its orientation. -/
theorem openMinorArc_swap (u v : Space) : openMinorArc u v = openMinorArc v u := by
  have reverse (x y : Space) : openMinorArc x y ⊆ openMinorArc y x := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith only [ht.2], by linarith only [ht.1]⟩, ?_⟩
    rw [sub_sub_cancel, add_comm]
  exact Set.Subset.antisymm (reverse u v) (reverse v u)

/-- If the two endpoint memberships differ, one of the actual selector
side portions is met in the open arc. -/
theorem exists_openMinorArc_inter_selector_side {I : Type*} [Finite I]
    (f : I → Space →ₗ[ℝ] ℝ) (edge : I → Set Space)
    {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (not_antipodal : u + v ≠ 0)
    (generic_u : ∀ i, f i u ≠ 0) (generic_v : ∀ i, f i v ≠ 0)
    (changed : ¬ ((∀ i, 0 ≤ f i u) ↔ (∀ i, 0 ≤ f i v)))
    (side : ∀ z ∈ Metric.sphere (0 : Space) 1, (∀ i, 0 ≤ f i z) →
      ∀ i, f i z = 0 → z ∈ edge i) :
    ∃ i, (openMinorArc u v ∩ edge i).Nonempty := by
  have witness {x y : Space} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (distinct : x + y ≠ 0)
      (generic : ∀ i, f i x ≠ 0) (inside : ∀ i, 0 ≤ f i x) (outside : ¬ ∀ i, 0 ≤ f i y) :
      ∃ i, (openMinorArc x y ∩ edge i).Nonempty := by
    obtain ⟨z, arc, unit, support, j, crossing⟩ := exists_openMinorArc_support_boundary f hx hy distinct
      (fun i => (inside i).lt_of_ne (generic i).symm) outside
    exact ⟨j, ⟨z, arc, side z unit support j crossing⟩⟩
  by_cases u_inside : ∀ i, 0 ≤ f i u
  · exact witness hu hv not_antipodal generic_u u_inside (fun v_inside =>
      changed (iff_of_true u_inside v_inside))
  · have v_inside : ∀ i, 0 ≤ f i v := by_contra fun v_outside =>
      changed (iff_of_false u_inside v_outside)
    rw [openMinorArc_swap]
    exact witness hv hu (by rwa [add_comm]) generic_v v_inside u_inside

end Unfoldings
