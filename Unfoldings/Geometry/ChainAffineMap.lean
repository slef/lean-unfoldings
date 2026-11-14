module

public import Unfoldings.Geometry.ChainPaths

/-! Affine images retain the entire actual polygonal chain carrier. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ℕ} (P : PolygonalChain E n)

def affineMap (A : E →ᵃ[ℝ] F) : PolygonalChain F n where
  vertex i := A (P.vertex i)

@[simp] theorem affineMap_point (A : E →ᵃ[ℝ] F) (i : Fin n) (t : unitInterval) :
    (P.affineMap A).point i t = A (P.point i t) :=
  (A.apply_lineMap _ _ _).symm

/-- Images include all edge interiors, shared endpoints and collapsed edges. -/
theorem affineMap_path_range (A : E →ᵃ[ℝ] F) :
    Set.range (P.affineMap A).path = A '' Set.range P.path := by
  rw [(P.affineMap A).path_range, P.path_range, Set.image_union, Set.image_singleton,
    Set.image_iUnion]
  congr 1
  apply Set.iUnion_congr
  intro i
  rw [← Set.range_comp]
  congr 1
  funext t
  exact P.affineMap_point A i t

end Unfoldings.PolygonalChain
