module

public import Unfoldings.Path.Length
public import Mathlib.Analysis.ConstantSpeed
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Bounded-speed replacements of rectifiable paths

These general metric-space results adapt `ArcLength.lean` and
`SurfaceReparameterization.lean` in slef/EdgeUnfoldings, snapshot
56caca8cdc44dbc2f839e93808088d56ea3f0780. The newer Mathlib continuity theorem
for accumulated variation removes the separate one-sided continuity argument.
-/

@[expose] public section

open Set Filter
open scoped ENNReal NNReal Topology

namespace Path

variable {X : Type*} [MetricSpace X] {a b : X}

/-- Pauses do not prevent continuity of the distance-travelled parameter. -/
theorem continuous_accumulated_length (p : Path a b) (finite : p.eLength ≠ ⊤) :
    Continuous (variationOnFromTo p Set.univ 0) := by
  have bounded : BoundedVariationOn p Set.univ := finite
  exact continuous_iff_continuousAt.mpr fun x =>
    (bounded.continuousAt_variationOnFromTo_iff 0 x).mpr p.continuous.continuousAt

theorem accumulated_length_image (p : Path a b) (finite : p.eLength ≠ ⊤) :
    variationOnFromTo p Set.univ 0 '' Set.univ = Set.Icc 0 p.eLength.toReal := by
  have bounded : BoundedVariationOn p Set.univ := finite
  have endpoints : (Set.Icc (0 : unitInterval) 1) = Set.univ := by
    ext t
    exact ⟨fun _ => mem_univ _, fun _ => t.property⟩
  have image := ContinuousOn.image_Icc_of_monotoneOn
    (show (0 : unitInterval) ≤ 1 from unitInterval.le_one')
    (p.continuous_accumulated_length finite).continuousOn
    ((variationOnFromTo.monotoneOn bounded.locallyBoundedVariationOn (mem_univ 0)).mono
      (subset_univ _))
  rwa [variationOnFromTo.self, variationOnFromTo.eq_of_le _ _ unitInterval.le_one',
    endpoints, inter_univ] at image

theorem unit_speed_lipschitz {g : ℝ → X} {s : Set ℝ}
    (speed : HasUnitSpeedOn g s) : LipschitzOnWith 1 g s := by
  intro x hx y hy
  wlog ordered : x ≤ y generalizing x y
  · simpa only [edist_comm] using this hy hx (le_of_not_ge ordered)
  have bound := eVariationOn.edist_le g
    (show x ∈ s ∩ Icc x y from ⟨hx, le_rfl, ordered⟩)
    (show y ∈ s ∩ Icc x y from ⟨hy, ordered, le_rfl⟩)
  rw [speed hx hy] at bound
  simpa only [NNReal.coe_one, one_mul, ENNReal.coe_one, edist_dist, Real.dist_eq,
    abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr ordered)] using bound

/-- Every rectifiable path has a bounded-speed replacement with exactly the same image. -/
theorem exists_lipschitz_reparameterization (p : Path a b) (finite : p.eLength ≠ ⊤) :
    ∃ q : Path a b, LipschitzWith p.eLength.toNNReal q ∧ Set.range q = Set.range p ∧
      q.eLength ≤ p.eLength := by
  have bounded : BoundedVariationOn p Set.univ := finite
  let L := p.eLength.toReal
  let g := naturalParameterization p Set.univ (0 : unitInterval)
  have covered : variationOnFromTo p Set.univ 0 '' Set.univ = Icc 0 L :=
    p.accumulated_length_image finite
  have same (t : unitInterval) : g (variationOnFromTo p Set.univ 0 t) = p t :=
    edist_eq_zero.mp (edist_naturalParameterization_eq_zero
      bounded.locallyBoundedVariationOn (mem_univ _) (mem_univ t))
  have natural_speed : LipschitzOnWith 1 g (Icc 0 L) := by
    rw [← covered]
    exact unit_speed_lipschitz (has_unit_speed_naturalParameterization _
      bounded.locallyBoundedVariationOn (mem_univ _))
  have in_interval (t : unitInterval) : L * (t : ℝ) ∈ Icc 0 L :=
    ⟨mul_nonneg ENNReal.toReal_nonneg t.property.1,
      mul_le_of_le_one_right ENNReal.toReal_nonneg t.property.2⟩
  let f : unitInterval → X := fun t => g (L * (t : ℝ))
  have speed : LipschitzWith p.eLength.toNNReal f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have bound := natural_speed.dist_le_mul _ (in_interval x) _ (in_interval y)
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, ← mul_sub, abs_mul,
      abs_of_nonneg (show 0 ≤ L from ENNReal.toReal_nonneg),
      ENNReal.coe_toNNReal_eq_toReal, Subtype.dist_eq, L] using bound
  have at_zero : f 0 = a := by
    change g (L * 0) = a
    simpa only [mul_zero, variationOnFromTo.self, Path.source] using same 0
  have at_one : f 1 = b := by
    have end_length : variationOnFromTo p Set.univ 0 1 = L := by
      rw [variationOnFromTo.eq_of_le _ _ unitInterval.le_one']
      have interval : Icc (0 : unitInterval) 1 = Set.univ := by
        ext t
        exact ⟨fun _ => mem_univ _, fun _ => t.property⟩
      rw [interval, inter_univ]
      rfl
    change g (L * 1) = b
    simpa only [mul_one, end_length, Path.target] using same 1
  have image : Set.range f = Set.range p := by
    apply Subset.antisymm
    · rintro _ ⟨t, rfl⟩
      obtain ⟨u, _, hu⟩ := covered.ge (in_interval t)
      exact ⟨u, by change p u = g (L * (t : ℝ)); rw [← hu, same]⟩
    · rintro _ ⟨t, rfl⟩
      by_cases zero : L = 0
      · refine ⟨0, ?_⟩
        have h := covered.le (mem_image_of_mem (variationOnFromTo p Set.univ 0) (mem_univ t))
        have ht : variationOnFromTo p Set.univ 0 t = 0 := by simpa [zero] using h
        change g (L * 0) = p t
        simpa only [mul_zero, ht] using same t
      · let s := variationOnFromTo p Set.univ 0 t
        have hs : s ∈ Icc 0 L := covered.le (mem_image_of_mem _ (mem_univ t))
        have positive : 0 < L := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm zero)
        refine ⟨⟨s / L, div_nonneg hs.1 positive.le, (div_le_one positive).mpr hs.2⟩, ?_⟩
        change g (L * (s / L)) = p t
        rw [mul_div_cancel₀ _ zero]
        exact same t
  let q : Path a b := ⟨⟨f, speed.continuous⟩, at_zero, at_one⟩
  refine ⟨q, speed, image, ?_⟩
  exact (q.eLength_le_of_lipschitz speed).trans_eq (ENNReal.coe_toNNReal finite)

end Path
