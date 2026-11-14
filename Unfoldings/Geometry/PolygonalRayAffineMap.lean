module

public import Unfoldings.Geometry.PolygonalRay
public import Unfoldings.Geometry.ChainAffineMap

/-! Affine maps retain finite polygonal banks and their actual straight infinite tails. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ℕ} (R : PolygonalRay E n)

def affineMap (A : E →ᵃ[ℝ] F) : PolygonalRay F n where
  chain := R.chain.affineMap A
  direction := A.linear R.direction

@[simp] theorem affineMap_start (A : E →ᵃ[ℝ] F) : (R.affineMap A).start = A R.start := rfl

@[simp] theorem affineMap_tail (A : E →ᵃ[ℝ] F) (t : ℝ≥0) :
    (R.affineMap A).tail t = A (R.tail t) := by
  change A (R.chain.vertex (Fin.last n)) + (t : ℝ) • A.linear R.direction =
    A (R.chain.vertex (Fin.last n) + (t : ℝ) • R.direction)
  have mapped := A.map_vadd (R.chain.vertex (Fin.last n)) ((t : ℝ) • R.direction)
  simpa only [vadd_eq_add, map_smul, add_comm] using mapped.symm

theorem affineMap_carrier (A : E →ᵃ[ℝ] F) : (R.affineMap A).carrier = A '' R.carrier := by
  have tails : Set.range (R.affineMap A).tail = A '' Set.range R.tail := by
    rw [← Set.range_comp]
    congr 1
    funext t
    exact R.affineMap_tail A t
  change Set.range (R.chain.affineMap A).path ∪ Set.range (R.affineMap A).tail = _
  rw [R.chain.affineMap_path_range, tails, carrier, Set.image_union]

end Unfoldings.PolygonalRay
