module

public import Unfoldings.Cap.JordanBankTurnBounds

/-! Signed Jordan comparisons share one curvature budget across disjoint lenses. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

open Classical in
/-- The signed Gauss–Bonnet contributions of disjoint lenses and the curvature
corrections at bank vertices together cost at most the actual cap curvature.
The correction is supported outside the interiors of the lenses. -/
theorem abs_sum_disjoint_jordan_errors_add_bank_le_total {I : Type*} [Fintype I]
    (J : I → Set Plane) (jordan : ∀ i, Schoenflies.IsJordanCurve (J i))
    (inside : ∀ i, J i ⊆ interior K.footprint)
    (avoids : ∀ i f, Disjoint (interior (K.projectedTriangle f).carrier) (J i))
    (separated : Pairwise fun i j => Disjoint
      (interior (PlanarTopology.closedJordanDomain (J i)))
      (interior (PlanarTopology.closedJordanDomain (J j))))
    (sign : I → ℝ) (sign_bound : ∀ i, |sign i| ≤ 1) (correction : C.Vertex Set.univ → ℝ)
    (correction_bound : ∀ w, |correction w| ≤ C.interiorAngularDefect Set.univ w)
    (off_bank : ∀ i w, K.projectedVertex w ∈ interior (PlanarTopology.closedJordanDomain (J i)) →
      correction w = 0) :
    |(∑ i, sign i * (∑ k, K.jordanContourTurnError (jordan i)
        ((inside i).trans interior_subset) (avoids i) k)) + ∑ w, correction w| ≤
      C.totalInteriorAngularDefect Set.univ := by
  let δ (w : C.Vertex Set.univ) := C.interiorAngularDefect Set.univ w
  let domain (i : I) := interior (PlanarTopology.closedJordanDomain (J i))
  let weight (i : I) (w : C.Vertex Set.univ) := if K.projectedVertex w ∈ domain i then δ w else 0
  let error (i : I) := ∑ k, K.jordanContourTurnError (jordan i)
    ((inside i).trans interior_subset) (avoids i) k
  have weight_nonneg (i : I) (w : C.Vertex Set.univ) : 0 ≤ weight i w := by
    unfold weight
    split_ifs <;> simp only [le_refl, δ, K.interiorCurvature_nonneg]
  have lens (i : I) : error i = -(∑ w, weight i w) :=
    K.jordan_contour_turn_comparison (jordan i) ((inside i).trans interior_subset)
      (avoids i) (inside i)
  have lens_bound (i : I) : |sign i * error i| ≤ ∑ w, weight i w := by
    rw [lens, abs_mul, abs_neg, abs_of_nonneg (Finset.sum_nonneg (fun w _ => weight_nonneg i w))]
    exact mul_le_of_le_one_left (Finset.sum_nonneg (fun w _ => weight_nonneg i w)) (sign_bound i)
  have spent (w : C.Vertex Set.univ) : (∑ i, weight i w) + |correction w| ≤ δ w := by
    by_cases enclosed : ∃ i, K.projectedVertex w ∈ domain i
    · obtain ⟨i, hit⟩ := enclosed
      have weight_eq : (∑ j, weight j w) = δ w := by
        calc
          (∑ j, weight j w) = weight i w := by
            apply Finset.sum_eq_single i
            · intro j _ different
              exact ite_eq_right (fun at_j => Set.disjoint_left.mp (separated different) at_j hit)
            · simp
          _ = δ w := ite_eq_left hit
      rw [weight_eq, off_bank i w hit, abs_zero, add_zero]
    · have absent (i : I) : weight i w = 0 :=
        ite_eq_right (fun hit => enclosed ⟨i, hit⟩)
      simp only [absent, Finset.sum_const_zero, zero_add, δ, correction_bound]
  have total : (∑ i, ∑ w, weight i w) + (∑ w, |correction w|) ≤
      C.totalInteriorAngularDefect Set.univ := by
    rw [Finset.sum_comm (f := weight), ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun w _ => spent w)
  calc
    _ ≤ |∑ i, sign i * error i| + |∑ w, correction w| := abs_add_le _ _
    _ ≤ (∑ i, ∑ w, weight i w) + (∑ w, |correction w|) :=
      add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => lens_bound i)))
        (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ _ := total

end Unfoldings.ConvexCap
