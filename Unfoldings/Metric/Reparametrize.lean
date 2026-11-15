module

public import Unfoldings.Metric.Quotient
public import Mathlib.Topology.MetricSpace.Isometry

/-! Cellwise isometries preserve the constructed gluing metric exactly. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {I : Type*} {E F : I → Type*} [∀ i, EMetricSpace (E i)] [∀ i, EMetricSpace (F i)]
  (A : ∀ i, E i ≃ᵢ F i) (glue : Total F → Total F → Prop)

/-- The same actual seam relation in different isometric cell coordinates. -/
def reparametrizeGlue (x y : Total E) : Prop :=
  glue ⟨x.1, A x.1 x.2⟩ ⟨y.1, A y.1 y.2⟩

/-- Change each cell's coordinates without changing any seam. -/
def reparametrize : Realization E (reparametrizeGlue A glue) → Realization F glue :=
  lift E (reparametrizeGlue A glue) (fun i => of F glue i ∘ A i)
    (fun i => by simpa only [one_mul] using
      (of_lipschitz F glue i).comp (A i).isometry.lipschitzWith)
    (fun _ _ joined => point_eq_of_glue F joined)

@[simp] theorem reparametrize_of (i : I) (x : E i) :
    reparametrize A glue (of E (reparametrizeGlue A glue) i x) = of F glue i (A i x) := rfl

theorem reparametrize_lipschitz : LipschitzWith 1 (reparametrize A glue) :=
  lift_lipschitz E (reparametrizeGlue A glue) _ _ _

/-- The inverse coordinate change uses the inverse of the very same cell isometries. -/
def reparametrizeInverse : Realization F glue → Realization E (reparametrizeGlue A glue) :=
  lift F glue (fun i => of E (reparametrizeGlue A glue) i ∘ (A i).symm)
    (fun i => by simpa only [one_mul] using
      (of_lipschitz E (reparametrizeGlue A glue) i).comp (A i).symm.isometry.lipschitzWith)
    (by
      intro x y joined
      apply point_eq_of_glue
      change glue ⟨x.1, A x.1 ((A x.1).symm x.2)⟩
        ⟨y.1, A y.1 ((A y.1).symm y.2)⟩
      simpa only [IsometryEquiv.apply_symm_apply] using joined)

@[simp] theorem reparametrizeInverse_of (i : I) (x : F i) :
    reparametrizeInverse A glue (of F glue i x) =
      of E (reparametrizeGlue A glue) i ((A i).symm x) := rfl

theorem reparametrizeInverse_lipschitz : LipschitzWith 1 (reparametrizeInverse A glue) :=
  lift_lipschitz F glue _ _ _

theorem reparametrize_leftInverse :
    Function.LeftInverse (reparametrizeInverse A glue) (reparametrize A glue) := by
  intro x
  obtain ⟨⟨i, p⟩, rfl⟩ := point_surjective E (reparametrizeGlue A glue) x
  change reparametrizeInverse A glue
    (reparametrize A glue (of E (reparametrizeGlue A glue) i p)) = _
  rw [reparametrize_of, reparametrizeInverse_of, IsometryEquiv.symm_apply_apply]
  rfl

theorem reparametrize_rightInverse :
    Function.RightInverse (reparametrizeInverse A glue) (reparametrize A glue) := by
  intro x
  obtain ⟨⟨i, p⟩, rfl⟩ := point_surjective F glue x
  change reparametrize A glue (reparametrizeInverse A glue (of F glue i p)) = _
  rw [reparametrizeInverse_of, reparametrize_of, IsometryEquiv.apply_symm_apply]
  rfl

/-- This is an isometry of the actual route-metric separation quotients. -/
def reparametrizeIsometryEquiv :
    Realization E (reparametrizeGlue A glue) ≃ᵢ Realization F glue where
  toFun := reparametrize A glue
  invFun := reparametrizeInverse A glue
  left_inv := reparametrize_leftInverse A glue
  right_inv := reparametrize_rightInverse A glue
  isometry_toFun := by
    intro x y
    apply le_antisymm
    · simpa only [ENNReal.coe_one, one_mul] using reparametrize_lipschitz A glue x y
    · have bound := reparametrizeInverse_lipschitz A glue
        (reparametrize A glue x) (reparametrize A glue y)
      simpa only [reparametrize_leftInverse A glue x, reparametrize_leftInverse A glue y,
        ENNReal.coe_one, one_mul] using bound

end Unfoldings.MetricGluing
