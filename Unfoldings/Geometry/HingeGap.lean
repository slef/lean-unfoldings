module

public import Unfoldings.Geometry.PolygonalRayOpening
public import Unfoldings.Geometry.PolygonalRaySuffix
public import Unfoldings.Geometry.PolygonalRayAffineMap
public import Unfoldings.Geometry.PolygonalGapCells

/-! Source-rotation gaps at actual internal hinges retain the exact moved infinite suffix. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n)

/-- The moved suffix is exactly the affine image about the current hinge, including its tail. -/
theorem rotateSuffix_suffix (hinge : Fin (n + 1)) (angle : ℝ) :
    (R.rotateSuffix hinge angle).suffix hinge = (R.suffix hinge).affineMap
      (sourceRotation (R.chain.vertex hinge) angle).toAffineMap := by
  have vertices : (fun i : Fin (n - hinge.val + 1) =>
      ((R.rotateSuffix hinge angle).suffix hinge).chain.vertex i) =
        (fun i => ((R.suffix hinge).affineMap
          (sourceRotation (R.chain.vertex hinge) angle).toAffineMap).chain.vertex i) := by
    funext i
    change (R.chain.rotateSuffix hinge angle).vertex ⟨hinge.val + i.val, by omega⟩ =
      sourceRotation (R.chain.vertex hinge) angle (R.chain.vertex ⟨hinge.val + i.val, by omega⟩)
    rw [R.chain.rotateSuffix_vertex_ge hinge angle _
      (by change hinge.val ≤ hinge.val + i.val; omega), sourceRotation_apply]
  have chains := congrArg (PolygonalChain.mk (E := ℂ) (n := n - hinge.val)) vertices
  have directions : (R.rotateSuffix hinge angle).direction =
      ((R.suffix hinge).affineMap
        (sourceRotation (R.chain.vertex hinge) angle).toAffineMap).direction := by
    rfl
  exact congrArg₂ (PolygonalRay.mk (E := ℂ) (n := n - hinge.val)) chains directions

theorem rotateSuffix_suffix_carrier (hinge : Fin (n + 1)) (angle : ℝ) :
    ((R.rotateSuffix hinge angle).suffix hinge).carrier =
      (R.suffix hinge).rotatedCarrier angle := by
  rw [R.rotateSuffix_suffix, (R.suffix hinge).affineMap_carrier]
  change (sourceRotation (R.chain.vertex hinge) angle) '' (R.suffix hinge).carrier = _
  simp only [rotatedCarrier, suffix_start, sourceRotation_apply]

/-- The gap's two banks are the actual old and opened suffixes at this hinge. -/
theorem hingeGap_frontier (hinge : Fin (n + 1)) (outward : (R.suffix hinge).Outward)
    (nonzero : R.direction ≠ 0) (angle : ℝ) (sine : Real.sin angle ≠ 0) :
    frontier ((R.suffix hinge).rotationGap outward nonzero angle) =
      (R.suffix hinge).carrier ∪ ((R.rotateSuffix hinge angle).suffix hinge).carrier := by
  rw [(R.suffix hinge).frontier_rotationGap outward nonzero angle sine,
    R.rotateSuffix_suffix_carrier]

theorem hingeGap_banks_inter (hinge : Fin (n + 1)) (outward : (R.suffix hinge).Outward)
    (nonzero : R.direction ≠ 0) (angle : ℝ) (distinct : polarRay angle ≠ 1) :
    (R.suffix hinge).carrier ∩ ((R.rotateSuffix hinge angle).suffix hinge).carrier =
      {R.chain.vertex hinge} := by
  rw [R.rotateSuffix_suffix_carrier,
    (R.suffix hinge).rotatedCarrier_inter outward nonzero angle distinct, R.suffix_start]

end Unfoldings.PolygonalRay
