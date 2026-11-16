module

public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.MetricSpace.Dilation

/-! Complete extended-metric targets retain the missing endpoint of a finite bank interval. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings

/-- Restrict a dilation to any isometric parameter subspace, retaining its exact ratio. -/
theorem dilation_comp_isometry_lipschitz {A B C : Type*} [PseudoEMetricSpace A]
    [PseudoEMetricSpace B] [PseudoEMetricSpace C] (g : B →ᵈ C) (f : A → B)
    (isometric : Isometry f) :
    LipschitzWith (Dilation.ratio g) (g ∘ f) := by
  intro s t
  exact (Dilation.lipschitzWith g (f s) (f t)).trans_eq
    (congrArg (fun d : ℝ≥0∞ => (Dilation.ratio g : ℝ≥0∞) * d) (isometric.edist_eq s t))

/-- Exact lifted distances retain a dilation's original ratio on an isometric parameter subspace. -/
def dilationOfIsometricLift {A B C Y : Type*} [PseudoEMetricSpace A] [PseudoEMetricSpace B]
    [PseudoEMetricSpace C] [PseudoEMetricSpace Y] (g : B →ᵈ C) (param : A → B)
    (isometric : Isometry param) (f : A → Y)
    (same : ∀ s t, edist (f s) (f t) = edist (g (param s)) (g (param t))) : A →ᵈ Y where
  toFun := f
  edist_eq' := ⟨Dilation.ratio g, Dilation.ratio_ne_zero g, fun s t =>
    (same s t).trans ((Dilation.edist_eq g _ _).trans
      (congrArg (fun d : ℝ≥0∞ => (Dilation.ratio g : ℝ≥0∞) * d) (isometric.edist_eq s t)))⟩

def nonnegativeIcoParameter {T : ℝ} (t : Set.Ico (0 : ℝ) T) : ℝ≥0 := ⟨t.val, t.property.1⟩

theorem nonnegativeIcoParameter_isometry {T : ℝ} :
    Isometry (nonnegativeIcoParameter (T := T)) := fun _ _ => rfl

variable {X : Type*} [EMetricSpace X] [CompleteSpace X] {T : ℝ}

/-- The half-open interval as the actual dense subspace of its closed interval. -/
def intervalBelowEndParameter (t : {t : Set.Icc (0 : ℝ) T // t.val < T}) : Set.Ico (0 : ℝ) T :=
  ⟨t.val.val, t.val.property.1, t.property⟩

theorem intervalBelowEndParameter_isometry :
    Isometry (intervalBelowEndParameter (T := T)) := fun _ _ => rfl

/-- The missing final endpoint is approached within the original closed interval. -/
theorem dense_intervalBelowEnd (positive : 0 < T) : Dense {t : Set.Icc (0 : ℝ) T | t.val < T} := by
  let S : Set (Set.Icc (0 : ℝ) T) := {t | t.val < T}
  have image : Subtype.val '' S = Set.Ico (0 : ℝ) T := by
    ext t
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.property.1, hq⟩
    · intro ht
      exact ⟨⟨t, ht.1, ht.2.le⟩, ht.2, rfl⟩
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro t
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  change t.val ∈ closure (Subtype.val '' S)
  rw [image, closure_Ico positive.ne]
  exact t.property

/-- Complete the finite bank interval without changing any original earlier value. -/
def extendHalfOpenInterval (positive : 0 < T) (f : Set.Ico (0 : ℝ) T → X) :
    Set.Icc (0 : ℝ) T → X :=
  (dense_intervalBelowEnd positive).extend (f ∘ intervalBelowEndParameter)

theorem extendHalfOpenInterval_lipschitz (positive : 0 < T) (f : Set.Ico (0 : ℝ) T → X)
    {c : ℝ≥0} (bounded : LipschitzWith c f) :
    LipschitzWith c (extendHalfOpenInterval positive f) := by
  apply (dense_intervalBelowEnd positive).lipschitzWith_extend
  simpa only [mul_one] using bounded.comp intervalBelowEndParameter_isometry.lipschitzWith

omit [CompleteSpace X] in
theorem extendHalfOpenInterval_before (positive : 0 < T) (f : Set.Ico (0 : ℝ) T → X)
    {c : ℝ≥0} (bounded : LipschitzWith c f) (t : Set.Icc (0 : ℝ) T) (before : t.val < T) :
    extendHalfOpenInterval positive f t = f ⟨t.val, t.property.1, before⟩ :=
  (dense_intervalBelowEnd positive).extend_eq
    (bounded.continuous.comp intervalBelowEndParameter_isometry.continuous) ⟨t, before⟩

/-- Continuous physical identities persist through completion of the original endpoint. -/
theorem map_extendHalfOpenInterval {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (positive : 0 < T) (f : Set.Ico (0 : ℝ) T → X) {c : ℝ≥0} (bounded : LipschitzWith c f)
    (F : X → Y) (continuous_F : Continuous F) (g : Set.Icc (0 : ℝ) T → Y)
    (continuous_g : Continuous g)
    (agrees : ∀ t : Set.Ico (0 : ℝ) T, F (f t) = g ⟨t.val, t.property.1, t.property.2.le⟩)
    (t : Set.Icc (0 : ℝ) T) : F (extendHalfOpenInterval positive f t) = g t := by
  have closed : IsClosed {s | F (extendHalfOpenInterval positive f s) = g s} :=
    isClosed_eq (continuous_F.comp (extendHalfOpenInterval_lipschitz positive f bounded).continuous)
      continuous_g
  have dense : Dense {s | F (extendHalfOpenInterval positive f s) = g s} :=
    (dense_intervalBelowEnd positive).mono (fun s hs => by
      change F (extendHalfOpenInterval positive f s) = g s
      rw [extendHalfOpenInterval_before positive f bounded s hs]
      exact agrees ⟨s.val, s.property.1, hs⟩)
  have member := dense t
  rw [closed.closure_eq] at member
  exact member

end Unfoldings
