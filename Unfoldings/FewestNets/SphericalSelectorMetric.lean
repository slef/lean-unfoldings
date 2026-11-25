module

public import Unfoldings.FewestNets.SphericalSelectorBoundary
public import Unfoldings.FewestNets.EndpointCrossingLocality

/-! Geometric data for both regimes of the spherical selector crossing estimate. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.SphericalSelectorBoundary

open InnerProductGeometry Real

variable {J : Type*} {region : Set Space}

/-- The sharp endpoint localization uses the maximum side length, the
nonincident side separation, and each endpoint's own corner angle. -/
structure MetricData (B : SphericalSelectorBoundary J region) where
  longest : ℝ
  longest_pos : 0 < longest
  longest_small : longest ≤ π / 2
  side_pos : ∀ i, 0 < angle (B.endpoint i false) (B.endpoint i true)
  side_le : ∀ i, angle (B.endpoint i false) (B.endpoint i true) ≤ longest
  separation : ℝ
  separation_pos : 0 < separation
  separation_small : separation ≤ 1 / 10
  separated : ∀ ⦃i j⦄, i ≠ j → (∀ a b, B.endpoint i a ≠ B.endpoint j b) →
    ∀ x ∈ networkEdge B.endpoint i, ∀ y ∈ networkEdge B.endpoint j, separation ≤ angle x y
  corner : J → Bool → ℝ
  corner_pos : ∀ i b, 0 < corner i b
  incident : ∀ ⦃i j a b⦄, i ≠ j → B.endpoint i a = B.endpoint j b →
    corner i a ≤ angle (minorArcTangent (B.endpoint i a) (B.endpoint i (!a)))
      (minorArcTangent (B.endpoint j b) (B.endpoint j (!b)))

namespace MetricData

variable {B : SphericalSelectorBoundary J region} (M : MetricData B)

include M in
theorem side_nonantipodal (j : J) : B.endpoint j false + B.endpoint j true ≠ 0 := by
  intro zero
  have opposite := eq_neg_of_add_eq_zero_right zero
  have left : B.endpoint j false ≠ 0 := norm_ne_zero_iff.mp (by rw [B.endpoint_unit]; norm_num)
  have length := M.side_le j
  rw [opposite, angle_self_neg_of_nonzero left] at length
  linarith only [length, M.longest_small, pi_pos]

/-- Radius factor for the endpoint portion of a side in a cell of diameter d. -/
def endpointFactor (i : J) (b : Bool) : ℝ :=
  M.longest / (sin M.longest * sin (min (M.corner i b) (π / 2)))

theorem endpointFactor_pos (i : J) (b : Bool) : 0 < M.endpointFactor i b := by
  apply div_pos M.longest_pos
  exact mul_pos
    (sin_pos_of_pos_of_lt_pi M.longest_pos (by linarith only [M.longest_small, pi_pos]))
    (sin_pos_of_pos_of_lt_pi (lt_min (M.corner_pos i b) pi_div_two_pos)
      ((min_le_right _ _).trans_lt (by linarith only [pi_pos])))

variable [Fintype J]

/-- The normalized sum of endpoint factors and the whole perimeter bound are
the two alternatives in the charge estimate. -/
def crossingBudget : ℝ :=
  max ((∑ j : J × Bool, M.endpointFactor j.1 j.2) / π)
    ((∑ j, angle (B.endpoint j false) (B.endpoint j true)) / (π * M.separation))

end MetricData
end Unfoldings.FewestNets.SphericalSelectorBoundary
