module

public import Unfoldings.Basic
public import Schoenflies.JordanSeparates
public import Schoenflies.CrosscutCells
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Group.Bounded

/-! Compact planar sets with an escape ray from every exterior point have connected complement. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

/-- Every point outside a nonempty closed convex set has an outward ray disjoint from it. -/
theorem exists_escape_ray_of_not_mem_closed_convex {S : Set Plane}
    (convex : Convex ℝ S) (closed : IsClosed S) (nonempty : S.Nonempty)
    {p : Plane} (outside : p ∉ S) :
    ∃ u : Plane, u ≠ 0 ∧ ∀ r : ℝ, 0 ≤ r → p + r • u ∉ S := by
  obtain ⟨functional, c, below, above⟩ :=
    geometric_hahn_banach_closed_point convex closed outside
  let u := (InnerProductSpace.toDual ℝ Plane).symm functional
  have pairing (z : Plane) : inner ℝ z u = functional z := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have nonzero : u ≠ 0 := by
    intro zero
    obtain ⟨s, member⟩ := nonempty
    have first := below s member
    rw [← pairing s, zero, inner_zero_right] at first
    rw [← pairing p, zero, inner_zero_right] at above
    linarith
  refine ⟨u, nonzero, ?_⟩
  intro r nonnegative member
  have upper := below _ member
  have positive : 0 ≤ functional u := by rw [← pairing]; exact real_inner_self_nonneg
  rw [map_add, map_smul, smul_eq_mul] at upper
  have := mul_nonneg nonnegative positive
  linarith

/-- A nonconstant closed ray is unbounded. -/
theorem not_isBounded_ray (p u : Plane) (nonzero : u ≠ 0) :
    ¬ Bornology.IsBounded ((fun r : ℝ => p + r • u) '' Set.Ici 0) := by
  intro bounded
  obtain ⟨R, bound⟩ := bounded.exists_norm_le
  have positive : 0 < ‖u‖ := norm_pos_iff.mpr nonzero
  let r : ℝ := (R + ‖p‖ + 1) / ‖u‖
  have bound_p := bound p ⟨0, le_rfl, by simp⟩
  have nonnegative : 0 ≤ R := (norm_nonneg p).trans bound_p
  have r_positive : 0 < r := by dsimp [r]; positivity
  have bound_ray := bound (p + r • u) ⟨r, r_positive.le, rfl⟩
  have triangle := norm_sub_le (p + r • u) p
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos r_positive] at triangle
  have product : r * ‖u‖ = R + ‖p‖ + 1 := by
    dsimp [r]
    exact div_mul_cancel₀ _ positive.ne'
  linarith

/-- A component containing a ray to infinity is unbounded. -/
theorem not_isBounded_component_of_escape_ray {S : Set Plane} {p u : Plane}
    (nonzero : u ≠ 0) (escape : ∀ r : ℝ, 0 ≤ r → p + r • u ∈ S) :
    ¬ Bornology.IsBounded (connectedComponentIn S p) := by
  have connected : IsPreconnected ((fun r : ℝ => p + r • u) '' Set.Ici 0) :=
    isPreconnected_Ici.image _ (by fun_prop)
  have contains : p ∈ (fun r : ℝ => p + r • u) '' Set.Ici 0 :=
    ⟨0, le_rfl, by simp⟩
  have subset : (fun r : ℝ => p + r • u) '' Set.Ici 0 ⊆ S := by
    rintro _ ⟨r, hr, rfl⟩
    exact escape r hr
  intro bounded
  exact not_isBounded_ray p u nonzero
    (bounded.subset (connected.subset_connectedComponentIn contains subset))

/-- A compact planar set has connected complement if every exterior point has a straight
ray to infinity in its complement. No regularity of the set's boundary is required. -/
theorem isConnected_compl_of_escape_rays {S : Set Plane} (compact : IsCompact S)
    (escape : ∀ p ∉ S, ∃ u : Plane, u ≠ 0 ∧
      ∀ r : ℝ, 0 ≤ r → p + r • u ∉ S) : IsConnected Sᶜ := by
  obtain ⟨base, outside, _, unique⟩ :=
    Schoenflies.exists_unique_unbounded_connectedComponentIn_compl compact
  have equality : Sᶜ = connectedComponentIn Sᶜ base := by
    apply Set.Subset.antisymm _ (connectedComponentIn_subset _ _)
    intro p hp
    obtain ⟨u, nonzero, ray⟩ := escape p hp
    have unbounded := not_isBounded_component_of_escape_ray (S := Sᶜ) (p := p) nonzero ray
    rw [← unique p hp unbounded]
    exact mem_connectedComponentIn hp
  rw [equality]
  exact isConnected_connectedComponentIn_iff.mpr outside

/-- A compact planar set with connected complement contains every bounded region enclosed
by any of its subsets. In particular it contains the inside of each Jordan curve it carries. -/
theorem inside_subset_of_isConnected_compl {S J : Set Plane} (compact : IsCompact S)
    (connected : IsConnected Sᶜ) (subset : J ⊆ S) : Schoenflies.inside J ⊆ S := by
  obtain ⟨base, _outside, unbounded, _⟩ :=
    Schoenflies.exists_unique_unbounded_connectedComponentIn_compl compact
  intro p inside
  by_contra omitted
  have inclusion : Sᶜ ⊆ connectedComponentIn Jᶜ p :=
    connected.isPreconnected.subset_connectedComponentIn omitted
      (Set.compl_subset_compl.mpr subset)
  exact unbounded (inside.2.subset ((connectedComponentIn_subset Sᶜ base).trans inclusion))

end Unfoldings.PlanarTopology
