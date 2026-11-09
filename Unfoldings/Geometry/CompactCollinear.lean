module

public import Unfoldings.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Topology.Order.Compact
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Compact convex subsets of a proper planar affine line are closed segments. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_segment_of_compact_convex_collinear {s : Set E} (compact : IsCompact s)
    (convex : Convex ℝ s) (nonempty : s.Nonempty) (collinear : Collinear ℝ s) :
    ∃ a ∈ s, ∃ b ∈ s, s = segment ℝ a b := by
  obtain ⟨p, hp⟩ := nonempty
  obtain ⟨v, coordinates⟩ := (collinear_iff_of_mem hp).mp collinear
  by_cases zero : v = 0
  · have singleton : s = {p} := by
      apply Set.Subset.antisymm
      · intro x hx
        obtain ⟨r, equal⟩ := coordinates x hx
        simpa [zero] using equal
      · exact Set.singleton_subset_iff.mpr hp
    exact ⟨p, hp, p, hp, by simpa using singleton⟩
  let parameter (x : E) := ⟪v, x - p⟫ / ⟪v, v⟫
  have continuous_parameter : Continuous parameter :=
    (continuous_const.inner (continuous_id.sub continuous_const)).div_const _
  have parameter_smul (r : ℝ) : parameter (r • v + p) = r := by
    simp only [parameter, add_sub_cancel_right, inner_smul_right]
    exact mul_div_cancel_right₀ r (inner_self_ne_zero.mpr zero)
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap p (v + p)
  have line_apply (r : ℝ) : line r = r • v + p := by
    simp [line, AffineMap.lineMap_apply]
  have recovers (x : E) (hx : x ∈ s) : line (parameter x) = x := by
    obtain ⟨r, equal⟩ := coordinates x hx
    change x = r • v + p at equal
    rw [equal, parameter_smul, line_apply]
  obtain ⟨a, ha, minimum⟩ := compact.exists_isMinOn ⟨p, hp⟩ continuous_parameter.continuousOn
  obtain ⟨b, hb, maximum⟩ := compact.exists_isMaxOn ⟨p, hp⟩ continuous_parameter.continuousOn
  refine ⟨a, ha, b, hb, Set.Subset.antisymm ?_ (convex.segment_subset ha hb)⟩
  intro x hx
  have between : parameter x ∈ segment ℝ (parameter a) (parameter b) := by
    rw [segment_eq_uIcc, Set.uIcc_of_le (minimum hb)]
    exact ⟨minimum hx, maximum hx⟩
  have image : line (parameter x) ∈ line '' segment ℝ (parameter a) (parameter b) :=
    ⟨parameter x, between, rfl⟩
  rw [image_segment ℝ line, recovers a ha, recovers b hb, recovers x hx] at image
  exact image

theorem collinear_of_affine_zero {s : Set Plane} (l : Plane →ᵃ[ℝ] ℝ) (nonzero : l ≠ 0)
    (vanishes : ∀ x ∈ s, l x = 0) : Collinear ℝ s := by
  rcases s.eq_empty_or_nonempty with rfl | nonempty
  · exact collinear_empty ℝ Plane
  let Z := (affineSpan ℝ ({0} : Set ℝ)).comap l
  have member_iff (x : Plane) : x ∈ Z ↔ l x = 0 := by simp [Z]
  have included : s ⊆ Z := fun x hx => (member_iff x).mpr (vanishes x hx)
  have proper : Z ≠ ⊤ := by
    intro top
    apply nonzero
    ext x
    exact (member_iff x).mp (top ▸ AffineSubspace.mem_top ℝ Plane x)
  have direction_proper : Z.direction ≠ ⊤ := by
    intro top
    exact proper ((AffineSubspace.direction_eq_top_iff_of_nonempty
      (nonempty.mono included)).mp top)
  have dimension : Module.finrank ℝ Z.direction ≤ 1 := by
    have less := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr direction_proper)
    have plane_dimension : Module.finrank ℝ Plane = 2 := by simp [Plane]
    rw [finrank_top, plane_dimension] at less
    omega
  apply collinear_iff_finrank_le_one.mpr
  have span_le : affineSpan ℝ s ≤ Z := affineSpan_le.mpr included
  have directions := AffineSubspace.direction_le span_le
  rw [direction_affineSpan] at directions
  exact (Submodule.finrank_mono directions).trans dimension

end Unfoldings
