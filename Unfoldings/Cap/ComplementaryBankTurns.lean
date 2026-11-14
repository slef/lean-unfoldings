module

public import Unfoldings.Complex.RegionalCornerPartition
public import Unfoldings.Cap.RegionalAngles

/-!
# The two one-sided bank turn errors differ by actual original curvature

Complementary fans use opposite exterior-turn conventions along the same
oriented path. Their difference is the original intrinsic angular defect,
independently of how many incident corners each fan contains.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Complementary original fan errors add to the actual intrinsic-minus-projected full star. -/
theorem regionalAngleExcess_add_compl (U : Set Face) (w : C.Vertex Set.univ) :
    K.regionalAngleExcess U w + K.regionalAngleExcess Uᶜ w =
      C.totalAngle Set.univ w - K.projectedTotalAngle Set.univ w := by
  rw [regionalAngleExcess, regionalAngleExcess,
    C.regionalCornerSum_add_compl]
  classical
  simp only [TriangleComplex.totalAngle, projectedTotalAngle, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases same : C.vertexOfCorner Set.univ c = w <;> simp [same]

/-- At an interior path vertex the right and left bank turn errors differ by minus curvature. -/
theorem complementary_bank_turn_error (U : Set Face) (w : C.Vertex Set.univ)
    (internal : ¬ C.IsBoundaryVertex Set.univ w) :
    K.regionalAngleExcess Uᶜ w - (-K.regionalAngleExcess U w) =
      -C.interiorAngularDefect Set.univ w := by
  have balance := K.regionalAngleExcess_add_compl U w
  rw [K.projectedTotalAngle_eq_two_pi w internal] at balance
  simp only [TriangleComplex.interiorAngularDefect, ite_eq_right internal]
  linarith

/-- Switching banks along any distinct interior path vertices costs at most total cap curvature. -/
theorem abs_sum_complementary_bank_turn_error_le (U : Set Face)
    (vertices : Finset (C.Vertex Set.univ))
    (internal : ∀ w ∈ vertices, ¬ C.IsBoundaryVertex Set.univ w) :
    |(∑ w ∈ vertices, K.regionalAngleExcess Uᶜ w) -
      (∑ w ∈ vertices, -K.regionalAngleExcess U w)| ≤
      C.totalInteriorAngularDefect Set.univ := by
  classical
  rw [← Finset.sum_sub_distrib]
  have equality :
      (∑ w ∈ vertices, (K.regionalAngleExcess Uᶜ w - (-K.regionalAngleExcess U w))) =
        ∑ w ∈ vertices, -C.interiorAngularDefect Set.univ w :=
    Finset.sum_congr rfl (fun w member => K.complementary_bank_turn_error U w (internal w member))
  rw [equality]
  rw [Finset.sum_neg_distrib, abs_neg,
    abs_of_nonneg (Finset.sum_nonneg (fun w _ => K.interiorCurvature_nonneg w))]
  exact K.sum_interiorAngularDefect_le_totalCurvature vertices

end Unfoldings.ConvexCap
