module

public import Unfoldings.Cone.AngularFibers

/-!
# Injectivity below one full turn

Below a full turn, equal closed-sector coordinates have the same real heading.
Consecutive banks are already glued in the slit fan, so its development is
injective, including on its boundary.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n)

theorem develop_injective_of_lt_full (small : A.totalAngle < 2 * Real.pi) :
    Function.Injective A.develop := by
  intro z w equal
  obtain ⟨⟨i, x⟩, rfl⟩ := MetricGluing.point_surjective A.Cell A.glue z
  obtain ⟨⟨j, y⟩, rfl⟩ := MetricGluing.point_surjective A.Cell A.glue w
  change A.place i x = A.place j y at equal
  by_cases zero : A.place i x = 0
  · exact (A.faceMap_eq_origin_of_place_zero i x zero).trans
      (A.faceMap_eq_origin_of_place_zero j y (equal.symm.trans zero)).symm
  · obtain ⟨r, θ, θbounds, θpoint⟩ := A.exists_place_polar i x
    obtain ⟨s, φ, φbounds, φpoint⟩ := A.exists_place_polar j y
    have radii : r = s := polar_radius_eq r s θ φ (θpoint.symm.trans (equal.trans φpoint))
    subst s
    have nonzero : r ≠ 0 := by
      intro radius_zero
      apply zero
      rw [θpoint, radius_zero]
      simp
    have θupper : θ < 2 * Real.pi :=
      (θbounds.2.trans (A.heading_le_totalAngle _)).trans_lt small
    have φupper : φ < 2 * Real.pi :=
      (φbounds.2.trans (A.heading_le_totalAngle _)).trans_lt small
    have θglobal : θ ∈ Set.Icc 0 (2 * Real.pi) :=
      ⟨(A.heading_nonneg _).trans θbounds.1, θupper.le⟩
    have φglobal : φ ∈ Set.Icc 0 (2 * Real.pi) :=
      ⟨(A.heading_nonneg _).trans φbounds.1, φupper.le⟩
    rcases polar_eq_heading_cases r nonzero θ φ θglobal φglobal
        (θpoint.symm.trans (equal.trans φpoint)) with same | ⟨_, last⟩ | ⟨last, _⟩
    · rw [← same] at φbounds φpoint
      exact A.faceMap_eq_of_same_heading i j x y r θ θbounds φbounds θpoint φpoint
    · exact False.elim (φupper.ne last)
    · exact False.elim (θupper.ne last)

end Unfoldings.AngularFan
