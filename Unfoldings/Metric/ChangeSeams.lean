module

public import Unfoldings.Metric.Quotient
public import Mathlib.Topology.MetricSpace.Isometry

/-! Replacing declared seams by identifications already valid in the metric quotient. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {I : Type*} (E : I → Type*) [∀ i, EMetricSpace (E i)]
  {R S : Total E → Total E → Prop}

/-- A change of seams that identifies only pairs already equal in the target realization. -/
def changeSeams (compatible : ∀ x y, R x y → point E S x = point E S y) :
    Realization E R → Realization E S :=
  lift E R (of E S) (of_lipschitz E S) compatible

@[simp] theorem changeSeams_point
    (compatible : ∀ x y, R x y → point E S x = point E S y) (x : Total E) :
    changeSeams E compatible (point E R x) = point E S x := rfl

theorem changeSeams_lipschitz
    (compatible : ∀ x y, R x y → point E S x = point E S y) :
    LipschitzWith 1 (changeSeams E compatible) :=
  lift_lipschitz E R (of E S) (of_lipschitz E S) compatible

/-- Relations generating the same metric identifications give the same actual metric. -/
def changeSeamsIsometryEquiv
    (forward : ∀ x y, R x y → point E S x = point E S y)
    (backward : ∀ x y, S x y → point E R x = point E R y) :
    Realization E R ≃ᵢ Realization E S where
  toFun := changeSeams E forward
  invFun := changeSeams E backward
  left_inv x := by
    obtain ⟨p, rfl⟩ := point_surjective E R x
    rfl
  right_inv x := by
    obtain ⟨p, rfl⟩ := point_surjective E S x
    rfl
  isometry_toFun := by
    intro x y
    apply le_antisymm
    · simpa only [ENNReal.coe_one, one_mul] using changeSeams_lipschitz E forward x y
    · have bound := changeSeams_lipschitz E backward
        (changeSeams E forward x) (changeSeams E forward y)
      obtain ⟨p, rfl⟩ := point_surjective E R x
      obtain ⟨q, rfl⟩ := point_surjective E R y
      simpa only [changeSeams_point, ENNReal.coe_one, one_mul] using bound

end Unfoldings.MetricGluing
