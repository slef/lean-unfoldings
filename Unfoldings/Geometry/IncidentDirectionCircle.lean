module

public import Unfoldings.Geometry.SegmentIncidentGerm

/-! The exact incident cut rays meet the unit direction circle in finitely many points. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonnegative geometric ray has exactly its normalized generator as a unit direction. -/
theorem eq_normalized_of_mem_nonnegativeRay {direction v : E}
    (member : v ∈ nonnegativeRay direction) (unit : ‖v‖ = 1) :
    v = ‖direction‖⁻¹ • direction := by
  obtain ⟨t, nonnegative, equal⟩ := member
  have nonzero : direction ≠ 0 := by
    intro zero
    rw [zero, smul_zero] at equal
    rw [equal, norm_zero] at unit
    exact zero_ne_one unit
  have norm_nonzero := norm_ne_zero_iff.mpr nonzero
  have product : t * ‖direction‖ = 1 := by
    simpa only [equal, norm_smul, Real.norm_of_nonneg nonnegative] using unit
  have coefficient : t = ‖direction‖⁻¹ := by
    simpa only [one_div] using (eq_div_iff norm_nonzero).mpr product
  rwa [coefficient] at equal

variable {K : Type*} [Finite K] (first last : K → Plane)

/-- At a genuine network vertex there are only finitely many excluded circle directions. -/
theorem finite_incident_unit_directions (x : Plane) :
    {v : Plane | v ∈ incidentSegmentDirections first last x ∧ ‖v‖ = 1}.Finite := by
  let directions (i : K × Bool) : Plane :=
    if i.2 then ‖last i.1 - x‖⁻¹ • (last i.1 - x) else
      ‖first i.1 - x‖⁻¹ • (first i.1 - x)
  apply (Set.finite_range directions).subset
  intro v member
  obtain ⟨k, on_ray⟩ := Set.mem_iUnion.mp member.1
  rcases on_ray with incoming | outgoing
  · by_cases incident : x = first k
    · have on_ray : v ∈ nonnegativeRay (last k - x) := by
        simpa only [ite_eq_left incident] using incoming
      exact ⟨(k, true), (eq_normalized_of_mem_nonnegativeRay on_ray member.2).symm⟩
    · simp only [ite_eq_right incident, Set.mem_empty_iff_false] at incoming
  · by_cases incident : x = last k
    · have on_ray : v ∈ nonnegativeRay (first k - x) := by
        simpa only [ite_eq_left incident] using outgoing
      exact ⟨(k, false), (eq_normalized_of_mem_nonnegativeRay on_ray member.2).symm⟩
    · simp only [ite_eq_right incident, Set.mem_empty_iff_false] at outgoing

end Unfoldings
