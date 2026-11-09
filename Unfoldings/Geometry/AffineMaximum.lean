module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Order.LocalExtr
public import Mathlib.Topology.Order.Basic

/-!
# Local maxima of affine functionals

An affine real functional with a local maximum on a normed space is constant.
Consequently a nonzero supporting functional is strictly below its supporting
level at every ambient interior point of the supported set.
-/

@[expose] public section

open Topology

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affine_linear_eq_zero_of_localMax (g : E →ᵃ[ℝ] ℝ) (y : E)
    (maximum : IsLocalMax g y) : g.linear = 0 := by
  by_contra nonzero
  obtain ⟨v, unit⟩ := LinearMap.surjective nonzero (1 : ℝ)
  let curve : ℝ → E := fun t => t • v + y
  have continuous : Continuous curve := (continuous_id.smul continuous_const).add continuous_const
  have at_zero : curve 0 = y := by simp only [curve, zero_smul, zero_add]
  have tendsto := continuous.tendsto (0 : ℝ)
  rw [at_zero] at tendsto
  have near : ∀ᶠ t in 𝓝 (0 : ℝ), g (curve t) ≤ g y := tendsto.eventually maximum
  obtain ⟨l, h, ⟨lzero, zeroh⟩, bound⟩ := mem_nhds_iff_exists_Ioo_subset.mp near
  obtain ⟨t, positive, small⟩ := exists_between zeroh
  have at_t := bound ⟨lzero.trans positive, small⟩
  change g (curve t) ≤ g y at at_t
  have formula : g (curve t) = t + g y := by
    change g ((t • v) +ᵥ y) = t + g y
    rw [g.map_vadd, map_smul, unit]
    simp only [smul_eq_mul, mul_one, vadd_eq_add]
  rw [formula] at at_t
  exact (not_le_of_gt (lt_add_of_pos_left (g y) positive)) at_t

theorem affine_eq_at_of_localMax (g : E →ᵃ[ℝ] ℝ) (y : E)
    (maximum : IsLocalMax g y) (z : E) : g z = g y := by
  have zero := affine_linear_eq_zero_of_localMax g y maximum
  have equal := g.map_vadd y (z - y)
  simpa only [zero, LinearMap.zero_apply, zero_vadd, vadd_eq_add, sub_add_cancel, zero_add]
    using equal

theorem supporting_functional_lt_on_interior (f : E →L[ℝ] ℝ) (nonzero : f ≠ 0)
    (s : Set E) (a : ℝ) (supported : ∀ z ∈ s, f z ≤ a) (x : E) (inside : x ∈ interior s) :
    f x < a := by
  have bound : f x ≤ a := supported x (interior_subset inside)
  apply lt_of_le_of_ne bound
  intro equal
  have maximum : IsLocalMax f.toLinearMap.toAffineMap x := by
    change ∀ᶠ z in 𝓝 x, f z ≤ f x
    exact Filter.mem_of_superset (mem_interior_iff_mem_nhds.mp inside)
      (fun z hz => (supported z hz).trans_eq equal.symm)
  have linear_zero := affine_linear_eq_zero_of_localMax f.toLinearMap.toAffineMap x maximum
  apply nonzero
  ext z
  exact congrArg (fun l : E →ₗ[ℝ] ℝ => l z) linear_zero

end Unfoldings
