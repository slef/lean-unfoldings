module

public import Unfoldings.Geometry.TwoBankGapSourceSector
public import Unfoldings.Geometry.PolygonalRayOpening

/-! The original source opening is the exact geometric sector angle, before later hinges. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- A genuine source rotation below a half-turn gives its exact unreduced sector angle. -/
theorem initialGapAngle_rotated (d : ℂ) (genuine : d ≠ 0) {θ : ℝ}
    (positive : 0 < θ) (small : θ < Real.pi) :
    initialGapAngle d (complexRotation θ d) = θ := by
  have norm_nonzero : (‖d‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr genuine)
  have ratio : (complexRotation θ d / (‖complexRotation θ d‖ : ℂ)) /
      (d / (‖d‖ : ℂ)) = polarRay θ := by
    rw [(complexRotation θ).norm_map, complexRotation_apply]
    field_simp
  unfold initialGapAngle
  rw [ratio]
  exact Circle.arg_exp (by linarith [Real.pi_pos]) small.le

namespace PolygonalChain

variable {n : ℕ}

/-- Later hinges leave the actual first link heading unchanged. -/
theorem openingHeading_first_of_later_hinges (events : List (Opening n)) (i : Fin n)
    (first : i.val = 0) (later : ∀ event ∈ events, event.hinge ≠ 0) :
    openingHeading events i = 0 := by
  have first_index : i.castSucc = 0 := Fin.ext first
  unfold openingHeading
  apply List.sum_eq_zero
  intro value member
  obtain ⟨event, present, rfl⟩ := List.mem_map.mp member
  rw [first_index]
  have after : ¬event.hinge ≤ 0 := by
    intro before
    exact later event present (le_antisymm before (Fin.zero_le _))
  exact ite_eq_right after

/-- The source opening is spent once; later non-source hinges add no source turn. -/
theorem openingHeading_source_cons (κ : ℝ) (events : List (Opening n)) (i : Fin n)
    (first : i.val = 0) (later : ∀ event ∈ events, event.hinge ≠ 0) :
    openingHeading (⟨0, κ⟩ :: events) i = κ := by
  have first_index : i.castSucc = 0 := Fin.ext first
  simp only [openingHeading, List.map_cons, List.sum_cons, first_index, le_refl, ite_true]
  have tail := openingHeading_first_of_later_hinges events i first later
  unfold openingHeading at tail
  rw [first_index] at tail
  rw [tail, add_zero]

end PolygonalChain
end Unfoldings
