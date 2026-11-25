module

public import Unfoldings.Geometry.TwoLinkRegularApex
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Fix a compact comparison region before constructing the old completion mesh. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n) (h k : Plane →L[ℝ] ℝ)
  (first : ∀ i, 0 < h (P.edge i)) (last : ∀ i, 0 < k (P.edge i))

include first last in
/-- The entire bank and both open choices of apex fit in one compact region
that depends only on the original chain and its two diagonal controls. -/
theorem exists_compact_twoLink_comparison_region
    (joint : Function.Bijective fun p => (h p, k p)) :
    ∃ region : Set Plane, IsCompact region ∧ Convex ℝ region ∧
      Set.range P.path ⊆ interior region ∧
      ∀ a ∈ Set.range P.path, ∀ b ∈ Set.range P.path,
        {c | c ∈ interior region ∧ h c < h a ∧ k b < k c}.Nonempty ∧
        {c | c ∈ interior region ∧ k c < k a ∧ h b < h c}.Nonempty := by
  let a₀ := P.vertex 0
  let b₀ := P.vertex (Fin.last n)
  let R := |h a₀| + |h b₀| + |k a₀| + |k b₀| + 2
  let region := {p : Plane | h p ∈ Set.Icc (-R) R ∧ k p ∈ Set.Icc (-R) R}
  let linear := h.toLinearMap.prod k.toLinearMap
  let coordinates := LinearEquiv.ofBijective linear joint
  let chart := coordinates.toContinuousLinearEquiv
  have region_eq :
      region = (fun t : ℝ × ℝ => chart.symm t) '' (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) := by
    ext p
    constructor
    · intro member
      exact ⟨chart p, member, chart.symm_apply_apply p⟩
    · rintro ⟨t, member, rfl⟩
      change chart (chart.symm t) ∈ Set.Icc (-R) R ×ˢ Set.Icc (-R) R
      rwa [chart.apply_symm_apply]
  have compact : IsCompact region := by
    rw [region_eq]
    exact (isCompact_Icc.prod isCompact_Icc).image chart.symm.continuous
  have convex : Convex ℝ region := by
    change Convex ℝ (linear ⁻¹' (Set.Icc (-R) R ×ˢ Set.Icc (-R) R))
    exact ((convex_Icc _ _).prod (convex_Icc _ _)).linear_preimage linear
  have interior_of_strict {p : Plane} (hp : h p ∈ Set.Ioo (-R) R)
      (kp : k p ∈ Set.Ioo (-R) R) : p ∈ interior region := by
    let openBox := (h ⁻¹' Set.Ioo (-R) R) ∩ (k ⁻¹' Set.Ioo (-R) R)
    have opens : IsOpen openBox :=
      (h.continuous.isOpen_preimage _ isOpen_Ioo).inter (k.continuous.isOpen_preimage _ isOpen_Ioo)
    have included : openBox ⊆ region := by
      intro q member
      change h q ∈ Set.Ioo (-R) R ∧ k q ∈ Set.Ioo (-R) R at member
      change h q ∈ Set.Icc (-R) R ∧ k q ∈ Set.Icc (-R) R
      exact ⟨⟨member.1.1.le, member.1.2.le⟩, ⟨member.2.1.le, member.2.2.le⟩⟩
    exact opens.subset_interior_iff.mpr included (show p ∈ openBox from ⟨hp, kp⟩)
  have bounds {p : Plane} (member : p ∈ Set.range P.path) :
      -R + 1 ≤ h p ∧ h p ≤ R - 1 ∧ -R + 1 ≤ k p ∧ k p ≤ R - 1 := by
    obtain ⟨hlo, hhi⟩ := P.path_linear_bounds h (fun i => (first i).le) member
    obtain ⟨klo, khi⟩ := P.path_linear_bounds k (fun i => (last i).le) member
    change h a₀ ≤ h p at hlo
    change h p ≤ h b₀ at hhi
    change k a₀ ≤ k p at klo
    change k p ≤ k b₀ at khi
    dsimp only [R]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [abs_nonneg (h a₀), abs_nonneg (h b₀),
      abs_nonneg (k a₀), abs_nonneg (k b₀), neg_abs_le (h a₀), le_abs_self (h b₀),
      neg_abs_le (k a₀), le_abs_self (k b₀)]
  refine ⟨region, compact, convex, ?_, ?_⟩
  · intro p member
    obtain ⟨hlo, hhi, klo, khi⟩ := bounds member
    exact interior_of_strict ⟨by linarith only [hlo], by linarith only [hhi]⟩
      ⟨by linarith only [klo], by linarith only [khi]⟩
  · intro a ha b hb
    obtain ⟨hlo₁, hhi₁, klo₁, khi₁⟩ := bounds ha
    obtain ⟨hlo₂, hhi₂, klo₂, khi₂⟩ := bounds hb
    constructor
    · obtain ⟨p, eq⟩ := joint.surjective (h a - 1 / 2, k b + 1 / 2)
      have x : h p = h a - 1 / 2 := congrArg Prod.fst eq
      have y : k p = k b + 1 / 2 := congrArg Prod.snd eq
      refine ⟨p, interior_of_strict ⟨?_, ?_⟩ ⟨?_, ?_⟩, ?_, ?_⟩ <;>
        linarith only [x, y, hlo₁, hhi₁, klo₂, khi₂]
    · obtain ⟨p, eq⟩ := joint.surjective (h b + 1 / 2, k a - 1 / 2)
      have x : h p = h b + 1 / 2 := congrArg Prod.fst eq
      have y : k p = k a - 1 / 2 := congrArg Prod.snd eq
      refine ⟨p, interior_of_strict ⟨?_, ?_⟩ ⟨?_, ?_⟩, ?_, ?_⟩ <;>
        linarith only [x, y, hlo₂, hhi₂, klo₁, khi₁]

end Unfoldings.PolygonalChain
