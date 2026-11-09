module

public import Unfoldings.Metric.Quotient

/-!
# Lipschitz descent through metric gluing

Compatible cell maps with a strictly positive finite uniform Lipschitz bound
descend to the route realization with that bound. Positivity matters for
disconnected realizations: zero times infinite distance is zero.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace Unfoldings.MetricGluing

universe u v

variable {ι : Type u} (E : ι → Type v) [∀ i, PseudoEMetricSpace (E i)]

theorem map_edist_le_mul {Y : Type*} [PseudoEMetricSpace Y]
    (glue : Total E → Total E → Prop) (K : ℝ≥0) (positive : 0 < K) (f : ∀ i, E i → Y)
    (bounded : ∀ i, LipschitzWith K (f i))
    (compatible : ∀ x y, glue x y → f x.1 x.2 = f y.1 y.2) (x y : Total E) :
    edist (f x.1 x.2) (f y.1 y.2) ≤ K * Route.distance (stepCost E glue) x y := by
  classical
  have step (a b : Total E) :
      edist (f a.1 a.2) (f b.1 b.2) ≤ K * stepCost E glue a b := by
    by_cases related : glue a b ∨ glue b a
    · have equal := related.elim (compatible a b) (fun h => (compatible b a h).symm)
      simp [stepCost, related, equal]
    · obtain ⟨i, a⟩ := a
      obtain ⟨j, b⟩ := b
      by_cases same : i = j
      · subst j
        simpa [stepCost, related, faceCost] using (bounded i).edist_le_mul a b
      · simp [stepCost, related, faceCost, same, ne_of_gt positive]
  let : Nonempty (Route (Total E) x y) := ⟨Route.step x y⟩
  rw [Route.distance, ENNReal.mul_iInf (by simp)]
  apply le_iInf
  intro route
  induction route with
  | nil a => simp [Route.length]
  | cons a b tail ih =>
    exact (edist_triangle _ _ _).trans
      ((add_le_add (step a b) ih).trans_eq (mul_add _ _ _).symm)

/-- Descend compatible uniformly Lipschitz maps with a positive bound. -/
noncomputable def liftLipschitz {Y : Type*} [EMetricSpace Y]
    (glue : Total E → Total E → Prop) (K : ℝ≥0) (positive : 0 < K) (f : ∀ i, E i → Y)
    (bounded : ∀ i, LipschitzWith K (f i))
    (compatible : ∀ x y, glue x y → f x.1 x.2 = f y.1 y.2) :
    Realization E glue → Y :=
  SeparationQuotient.lift (fun x : PreSpace E glue => f x.1 x.2) (by
    intro x y inseparable
    apply edist_eq_zero.mp
    apply le_antisymm _ bot_le
    have bound := map_edist_le_mul E glue K positive f bounded compatible x y
    change edist (f x.1 x.2) (f y.1 y.2) ≤ K * edist x y at bound
    rw [EMetric.inseparable_iff.mp inseparable, mul_zero] at bound
    exact bound)

@[simp] theorem liftLipschitz_point {Y : Type*} [EMetricSpace Y]
    (glue : Total E → Total E → Prop) (K : ℝ≥0) (positive : 0 < K) (f : ∀ i, E i → Y)
    (bounded : ∀ i, LipschitzWith K (f i))
    (compatible : ∀ x y, glue x y → f x.1 x.2 = f y.1 y.2) (x : Total E) :
    liftLipschitz E glue K positive f bounded compatible (point E glue x) = f x.1 x.2 := rfl

theorem liftLipschitz_lipschitz {Y : Type*} [EMetricSpace Y]
    (glue : Total E → Total E → Prop) (K : ℝ≥0) (positive : 0 < K) (f : ∀ i, E i → Y)
    (bounded : ∀ i, LipschitzWith K (f i))
    (compatible : ∀ x y, glue x y → f x.1 x.2 = f y.1 y.2) :
    LipschitzWith K (liftLipschitz E glue K positive f bounded compatible) := by
  intro a b
  obtain ⟨x, rfl⟩ := point_surjective E glue a
  obtain ⟨y, rfl⟩ := point_surjective E glue b
  exact map_edist_le_mul E glue K positive f bounded compatible x y

end Unfoldings.MetricGluing
