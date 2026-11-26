module

public import Unfoldings.FewestNets.LatitudeFiniteSites

/-! Data for a latitude mesh, independent of the numerical choices of row sizes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

/-- A row specification supplies locations and sample counts independently.
The polar fans use the first and last numbered rows. -/
structure LatitudeRings where
  stripCount : ℕ
  colatitude : ℕ → ℝ
  rowSize : ℕ → ℕ

namespace LatitudeRings

/-- The combinatorial count of all annular midpoint advances. -/
def triangleCount (G : LatitudeRings) : ℕ :=
  ∑ j ∈ Finset.range G.stripCount, (G.rowSize j + G.rowSize (j + 1))

/-- The small conditions on the ring locations used by the spherical partition. -/
structure Admissible (G : LatitudeRings) : Prop where
  validColatitude : ∀ j ≤ G.stripCount, G.colatitude j ∈ Set.Ioo 0 π
  rowSize_ge_three : ∀ j ≤ G.stripCount, 3 ≤ G.rowSize j
  southern : cos (G.colatitude G.stripCount) < 0

/-- The angular spacing of the sites on a row. -/
def longitudeStep (G : LatitudeRings) (j : ℕ) : ℝ := 2 * π / G.rowSize j

variable {G : LatitudeRings} (hG : G.Admissible)
include hG

theorem rowSize_pos {j : ℕ} (valid : j ≤ G.stripCount) : 0 < G.rowSize j :=
  lt_of_lt_of_le (by decide) (hG.rowSize_ge_three j valid)

theorem colatitude_mem {j : ℕ} (valid : j ≤ G.stripCount) : G.colatitude j ∈ Set.Ioo 0 π :=
  hG.validColatitude j valid

theorem longitudeStep_pos_lt_pi {j : ℕ} (valid : j ≤ G.stripCount) :
    0 < G.longitudeStep j ∧ G.longitudeStep j < π := by
  have three : (3 : ℝ) ≤ (G.rowSize j : ℝ) := by exact_mod_cast hG.rowSize_ge_three j valid
  have count : 0 < (G.rowSize j : ℝ) := Nat.cast_pos.mpr (rowSize_pos hG valid)
  unfold longitudeStep
  refine ⟨div_pos (by positivity) count, (div_lt_iff₀ count).mpr ?_⟩
  rw [mul_comm 2 π]
  exact mul_lt_mul_of_pos_left (show (2 : ℝ) < G.rowSize j by linarith only [three]) pi_pos

end LatitudeRings
end Unfoldings.FewestNets
