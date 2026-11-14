module

public import Unfoldings.Metric.Lipschitz
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order.Bornology
public import Mathlib.Topology.Instances.Real.Lemmas

/-! Completeness of finite noncompact gluings from compatible cellwise coercive heights. -/

@[expose] public section

noncomputable section

open Filter Topology
open scoped NNReal

namespace Unfoldings.MetricGluing

universe u v

variable {ι : Type u} [Finite ι] (E : ι → Type v) [∀ i, PseudoEMetricSpace (E i)]
  (glue : Total E → Total E → Prop) (K : ℝ≥0) (positive : 0 < K)
  (height : ∀ i, E i → ℝ) (bounded : ∀ i, LipschitzWith K (height i))
  (compatible : ∀ x y, glue x y → height x.1 x.2 = height y.1 y.2)
  (compact_sublevels : ∀ i r, IsCompact {x : E i | height i x ≤ r})

include compact_sublevels in
/-- Every sublevel is the finite union of the compact cell sublevels' metric images. -/
theorem compact_sublevel_liftLipschitz (r : ℝ) :
    IsCompact {p : Realization E glue |
      liftLipschitz E glue K positive height bounded compatible p ≤ r} := by
  have equal : {p : Realization E glue |
      liftLipschitz E glue K positive height bounded compatible p ≤ r} =
        ⋃ i, of E glue i '' {x : E i | height i x ≤ r} := by
    ext p
    constructor
    · intro below
      obtain ⟨⟨i, x⟩, rfl⟩ := point_surjective E glue p
      exact Set.mem_iUnion.mpr ⟨i, x, below, rfl⟩
    · intro member
      obtain ⟨i, x, below, rfl⟩ := Set.mem_iUnion.mp member
      exact below
  rw [equal]
  exact isCompact_iUnion (fun i => (compact_sublevels i r).image (of_lipschitz E glue i).continuous)

include K positive height bounded compatible compact_sublevels in
/-- Cellwise compact sublevels prevent finite-distance escape to infinity. The cells themselves
need not be compact, and exactness of the seam quotient is not assumed. -/
theorem completeSpace_of_compact_sublevels : CompleteSpace (Realization E glue) := by
  let H := liftLipschitz E glue K positive height bounded compatible
  have lipschitz : LipschitzWith K H :=
    liftLipschitz_lipschitz E glue K positive height bounded compatible
  apply UniformSpace.complete_of_cauchySeq_tendsto
  intro sequence cauchy
  have image : CauchySeq (H ∘ sequence) := lipschitz.uniformContinuous.comp_cauchySeq cauchy
  obtain ⟨r, upper⟩ := image.isBounded_range.bddAbove
  have compact : IsCompact {p | H p ≤ r} :=
    compact_sublevel_liftLipschitz E glue K positive height bounded compatible compact_sublevels r
  obtain ⟨p, _member, converges⟩ := cauchySeq_tendsto_of_isComplete compact.isComplete
    (fun n => upper ⟨n, rfl⟩) cauchy
  exact ⟨p, converges⟩

end Unfoldings.MetricGluing
