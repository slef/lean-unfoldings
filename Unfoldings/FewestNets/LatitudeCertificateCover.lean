module

public import Unfoldings.FewestNets.LatitudeChargeIntervals

/-! Consecutive fixed-point intervals covering the numerical range. -/

@[expose] public section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real

/-- Breakpoints at precision `countPrecision`. Smaller intervals are used near
row-count changes and where the angular count approaches the target. -/
def latitudeCertificateBreakpoints : Array ℤ := #[
  31000000000000, 31500000000000, 32000000000000, 32500000000000, 33000000000000, 33500000000000,
  34000000000000, 34500000000000, 35000000000000, 35500000000000, 36000000000000, 36500000000000,
  37000000000000, 37500000000000, 38000000000000, 38500000000000, 39000000000000, 39500000000000,
  40000000000000, 40500000000000, 41000000000000, 41500000000000, 42000000000000, 42500000000000,
  43000000000000, 43500000000000, 44000000000000, 44500000000000, 45000000000000, 45500000000000,
  46000000000000, 46500000000000, 47000000000000, 47500000000000, 48000000000000, 48250000000000,
  48500000000000, 48750000000000, 48875000000000, 49000000000000, 49250000000000, 49500000000000,
  50000000000000, 50500000000000, 51000000000000, 51250000000000, 51500000000000, 51750000000000,
  52000000000000, 52179938779916, 52269908169874, 52314892864853, 52337385212342, 52348631386087,
  52354254472959, 52359877559832]

def latitudeCertificateEndpoint (k : ℕ) : ℤ :=
  latitudeCertificateBreakpoints[k]?.getD 52359877559832

/-- Every interval uses two consecutive endpoints from the same table. -/
def latitudeCertificateInterval (k : ℕ) : CountInterval :=
  ⟨latitudeCertificateEndpoint k, latitudeCertificateEndpoint (k + 1)⟩

/-- Every real angle in the numerical range lies in a checked interval. -/
theorem exists_latitudeCertificateInterval {a : ℝ} (lower : 0.31 ≤ a) (upper : a ≤ π / 6) :
    ∃ k : Fin 55, (latitudeCertificateInterval k).Contains a := by
  classical
  let x := a * (countPrecision : ℝ)
  have xlo : (latitudeCertificateEndpoint 0 : ℝ) ≤ x := by
    change ((31000000000000 : ℤ) : ℝ) ≤ a * (countPrecision : ℝ)
    norm_num [countPrecision]
    linarith only [lower]
  have xhi : x ≤ (latitudeCertificateEndpoint (54 + 1) : ℝ) := by
    change a * (countPrecision : ℝ) ≤ ((52359877559832 : ℤ) : ℝ)
    norm_num [countPrecision]
    linarith only [upper, pi_lt_d20]
  have covered : ∃ j : ℕ, x ≤ (latitudeCertificateEndpoint (j + 1) : ℝ) := ⟨54, xhi⟩
  let k := Nat.find covered
  have k_small : k ≤ 54 := Nat.find_min' covered xhi
  refine ⟨⟨k, by omega⟩, ?_⟩
  change (latitudeCertificateEndpoint k : ℝ) ≤ x ∧ x ≤ (latitudeCertificateEndpoint (k + 1) : ℝ)
  refine ⟨?_, Nat.find_spec covered⟩
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rwa [hk]
  · obtain ⟨j, j_eq⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    have lt : j < k := by omega
    have bad := Nat.find_min covered lt
    apply le_of_lt
    rw [j_eq]
    exact lt_of_not_ge bad

end Unfoldings.FewestNets.RevisedLatitudeGrid
