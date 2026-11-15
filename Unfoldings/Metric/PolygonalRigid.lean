module

public import Unfoldings.Metric.Polygonal
public import Mathlib.Analysis.Normed.Affine.Isometry

/-! Rigid changes of physical coordinates preserve the actual intrinsic polygonal metric. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.PolygonalPoint

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} {t : Set F}

/-- Map the actual points of a region using an ambient affine isometry. -/
def mapAffineIsometry (A : E →ᵃⁱ[ℝ] F) (included : ∀ x ∈ s, A x ∈ t) :
    PolygonalPoint s → PolygonalPoint t := fun x => ⟨A x.val, included x.val x.property⟩

theorem mapAffineIsometry_lipschitz (A : E →ᵃⁱ[ℝ] F) (included : ∀ x ∈ s, A x ∈ t) :
    LipschitzWith 1 (mapAffineIsometry A included) := by
  intro x y
  simp only [ENNReal.coe_one, one_mul]
  change edist (mapAffineIsometry A included x) (mapAffineIsometry A included y) ≤
    Route.distance stepCost x y
  apply Route.le_distance stepCost
    (fun a b => edist (mapAffineIsometry A included a) (mapAffineIsometry A included b))
    (fun _ => edist_self _) (fun _ _ _ => edist_triangle _ _ _)
  intro a b
  by_cases inside : segment ℝ a.val b.val ⊆ s
  · rw [stepCost, ite_eq_left inside]
    have segment_inside : segment ℝ (A a.val) (A b.val) ⊆ t := by
      change segment ℝ (A.toAffineMap a.val) (A.toAffineMap b.val) ⊆ t
      rw [← image_segment ℝ A.toAffineMap]
      rintro _ ⟨z, member, rfl⟩
      exact included z (inside member)
    exact (edist_eq_of_segment segment_inside).trans (A.isometry a.val b.val) |>.le
  · simp only [stepCost, ite_eq_right inside, le_top]

/-- Rigidly equivalent regions have exactly the same intrinsic polygonal metric,
including at reentrant corners and in unbounded regions. -/
def affineRegionIsometryEquiv (A : E ≃ᵃⁱ[ℝ] F) (cover : t = A '' s) :
    PolygonalPoint s ≃ᵢ PolygonalPoint t := by
  have forward : ∀ x ∈ s, A x ∈ t := by
    intro x member
    rw [cover]
    exact ⟨x, member, rfl⟩
  have backward : ∀ y ∈ t, A.symm y ∈ s := by
    intro y member
    rw [cover] at member
    obtain ⟨x, hx, rfl⟩ := member
    simpa only [AffineIsometryEquiv.symm_apply_apply] using hx
  let f := mapAffineIsometry A.toAffineIsometry forward
  let g := mapAffineIsometry A.symm.toAffineIsometry backward
  have left : Function.LeftInverse g f := fun x =>
    PolygonalPoint.ext (A.symm_apply_apply x.val)
  have right : Function.RightInverse g f := fun y =>
    PolygonalPoint.ext (A.apply_symm_apply y.val)
  refine ⟨⟨f, g, left, right⟩, ?_⟩
  intro x y
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul] using
      mapAffineIsometry_lipschitz A.toAffineIsometry forward x y
  · have bound := mapAffineIsometry_lipschitz A.symm.toAffineIsometry backward (f x) (f y)
    change edist (g (f x)) (g (f y)) ≤ (1 : ℝ≥0∞) * edist (f x) (f y) at bound
    simpa only [left x, left y, one_mul] using bound

@[simp] theorem affineRegionIsometryEquiv_val (A : E ≃ᵃⁱ[ℝ] F) (cover : t = A '' s)
    (x : PolygonalPoint s) : (affineRegionIsometryEquiv A cover x).val = A x.val := rfl

end Unfoldings.PolygonalPoint
