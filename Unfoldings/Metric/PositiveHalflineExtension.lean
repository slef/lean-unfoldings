module

public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Order.DenselyOrdered

/-! Complete extended-metric targets supply the exact endpoint of a positive Lipschitz ray. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

variable {X : Type*} [EMetricSpace X] [CompleteSpace X]

/-- Positive nonnegative-real parameters carry exactly their original real metric. -/
def positiveRealParameter (t : Set.Ioi (0 : ℝ≥0)) : Set.Ioi (0 : ℝ) :=
  ⟨t.val.val, t.property⟩

theorem positiveRealParameter_isometry : Isometry positiveRealParameter := fun _ _ => rfl

theorem dense_positiveHalfline : Dense (Set.Ioi (0 : ℝ≥0)) := by
  rw [dense_iff_closure_eq, closure_Ioi]
  apply Set.eq_univ_of_forall
  intro t
  exact t.property

/-- Complete the missing endpoint of a positive ray, retaining all positive values. -/
def extendPositiveHalfline (f : Set.Ioi (0 : ℝ) → X) : ℝ≥0 → X :=
  dense_positiveHalfline.extend (f ∘ positiveRealParameter)

theorem extendPositiveHalfline_lipschitz (f : Set.Ioi (0 : ℝ) → X) {c : ℝ≥0}
    (bounded : LipschitzWith c f) : LipschitzWith c (extendPositiveHalfline f) := by
  apply dense_positiveHalfline.lipschitzWith_extend
  simpa only [mul_one] using bounded.comp positiveRealParameter_isometry.lipschitzWith

omit [CompleteSpace X] in
theorem extendPositiveHalfline_positive (f : Set.Ioi (0 : ℝ) → X) {c : ℝ≥0}
    (bounded : LipschitzWith c f) (t : ℝ≥0) (positive : 0 < t) :
    extendPositiveHalfline f t = f ⟨t.val, positive⟩ :=
  dense_positiveHalfline.extend_eq
    (bounded.continuous.comp positiveRealParameter_isometry.continuous) ⟨t, positive⟩

/-- Continuous identities along a positive ray survive its metric endpoint completion. -/
theorem map_extendPositiveHalfline {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (f : Set.Ioi (0 : ℝ) → X) {c : ℝ≥0} (bounded : LipschitzWith c f)
    (F : X → Y) (continuous_F : Continuous F) (g : ℝ≥0 → Y) (continuous_g : Continuous g)
    (agrees : ∀ t : Set.Ioi (0 : ℝ), F (f t) = g ⟨t.val, t.property.le⟩)
    (t : ℝ≥0) : F (extendPositiveHalfline f t) = g t := by
  have closed : IsClosed {s | F (extendPositiveHalfline f s) = g s} :=
    isClosed_eq (continuous_F.comp (extendPositiveHalfline_lipschitz f bounded).continuous)
      continuous_g
  have dense : Dense {s | F (extendPositiveHalfline f s) = g s} :=
    dense_positiveHalfline.mono (fun s hs => by
      change F (extendPositiveHalfline f s) = g s
      rw [extendPositiveHalfline_positive f bounded s hs]
      exact agrees ⟨s.val, hs⟩)
  have member := dense t
  rw [closed.closure_eq] at member
  exact member

end Unfoldings
