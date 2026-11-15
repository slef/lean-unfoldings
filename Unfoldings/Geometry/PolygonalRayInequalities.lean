module

public import Unfoldings.Geometry.PolygonalRay
public import Unfoldings.Geometry.SegmentInequalities

/-! The exact original finite bends and unbounded tail as finite affine cut pieces. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

namespace PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n)

theorem range_point_eq_segment (i : Fin n) :
    Set.range (P.point i) = segment ℝ (P.vertex i.castSucc) (P.vertex i.succ) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact lineMap_mem_segment ℝ _ _ t.property
  · intro member
    rw [segment_eq_image_lineMap] at member
    obtain ⟨t, ht, rfl⟩ := member
    exact ⟨⟨t, ht⟩, rfl⟩

end PolygonalChain

namespace PolygonalRay

variable {n : ℕ} (R : PolygonalRay Plane n)

/-- Include the starting point, every original finite edge and the entire terminal ray. -/
def carrierInequalities : Unit ⊕ (Fin n ⊕ Unit) → Fin 6 → Plane →ᵃ[ℝ] ℝ :=
  Sum.elim (fun _ => segmentInequalities R.start R.start)
    (Sum.elim (fun i => segmentInequalities (R.chain.vertex i.castSucc) (R.chain.vertex i.succ))
      (fun _ => rayInequalities (R.chain.vertex (Fin.last n))
        (R.chain.vertex (Fin.last n) + R.direction)))

theorem range_tail_eq_closedChamber :
    Set.range R.tail = AffineArrangement.closedChamber
      (rayInequalities (R.chain.vertex (Fin.last n))
        (R.chain.vertex (Fin.last n) + R.direction)) (fun _ => true) := by
  rw [← ray_eq_closedChamber]
  congr 1
  funext t
  simp only [tail, AffineMap.lineMap_apply_module', add_sub_cancel_left]
  exact add_comm _ _

/-- This covers the actual entire ray, with no nonzero-edge, simplicity or nonoverlap premise. -/
theorem carrier_eq_iUnion_closedChamber :
    R.carrier = ⋃ i, AffineArrangement.closedChamber (R.carrierInequalities i) (fun _ => true) := by
  rw [carrier, R.chain.path_range]
  simp only [Set.iUnion_sum, carrierInequalities, Sum.elim_inl, Sum.elim_inr,
    Set.iUnion_const]
  simp_rw [← segment_eq_closedChamber, ← R.range_tail_eq_closedChamber,
    ← R.chain.range_point_eq_segment, segment_same]
  exact Set.union_assoc _ _ _

end PolygonalRay
end Unfoldings
