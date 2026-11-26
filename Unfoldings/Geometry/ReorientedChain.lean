module

public import Unfoldings.Geometry.PolygonalBankTailGerm
public import Unfoldings.Geometry.TwoLinkMonotoneChain

/-! Orthogonal reorientation preserves a chain and its two-link closing path. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n) (E : Plane ≃ₗᵢ[ℝ] Plane)

def reorient : PolygonalChain Plane n := ⟨fun i => E (P.vertex i)⟩

@[simp] theorem reorient_vertex (i : Fin (n + 1)) : (P.reorient E).vertex i = E (P.vertex i) :=
  rfl

@[simp] theorem reorient_edge (i : Fin n) : (P.reorient E).edge i = E (P.edge i) :=
  (map_sub E _ _).symm

theorem path_range_reorient : Set.range (P.reorient E).path = E '' Set.range P.path := by
  rw [P.path_range_eq_segments, (P.reorient E).path_range_eq_segments, Set.image_union,
    Set.image_singleton, Set.image_iUnion]
  simp only [reorient_vertex]
  have seg (a b : Plane) : E '' segment ℝ a b = segment ℝ (E a) (E b) :=
    image_segment ℝ E.toLinearEquiv.toLinearMap.toAffineMap _ _
  simp only [seg]

theorem forwardClosingChain_reorient (c : Plane) :
    (P.reorient E).forwardClosingChain (E c) = (P.forwardClosingChain c).reorient E := by
  change (⟨![E (P.vertex 0), E c, E (P.vertex (Fin.last n))]⟩ : PolygonalChain Plane 2) =
    ⟨fun i => E (![P.vertex 0, c, P.vertex (Fin.last n)] i)⟩
  congr 1
  funext i
  fin_cases i <;> rfl

theorem lineMap_reorient (p q : Plane) (t : ℝ) :
    AffineMap.lineMap (E p) (E q) t = E (AffineMap.lineMap p q t) := by
  simp only [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub]

end Unfoldings.PolygonalChain
