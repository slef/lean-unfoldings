module

public import Unfoldings.Geometry.Affine

/-! Construction of rigid hinge placements with strict opposite-side opening. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- A rigid placement of the second triangle, with the first triangle fixed in its own plane. -/
structure HingePlacement (T U : Triangle) (e f : Fin 3) (identify : T.Edge e ≃ᵢ U.Edge f) where
  place : Plane ≃ᵃⁱ[ℝ] Plane
  joined : ∀ x : T.Edge e, place (identify x).val = x.val
  opposite : orient (T.vertex e) (T.vertex (Triangle.next e)) (T.opposite e) *
    orient (T.vertex e) (T.vertex (Triangle.next e)) (place (U.opposite f)) < 0

/-- Full-edge isometric pairings always admit an outward rigid hinge placement. -/
theorem exists_hingePlacement (T U : Triangle) (e f : Fin 3) (identify : T.Edge e ≃ᵢ U.Edge f) :
    Nonempty (HingePlacement T U e f identify) := by
  let g : U.Edge f → Plane := fun x => (identify.symm x).val
  have isometry : Isometry g := fun x y => identify.symm.isometry x y
  obtain ⟨F, extension⟩ := exists_affineIsometry_extension_segment g isometry
  have joined (x : T.Edge e) : F (identify x).val = x.val :=
    (extension (identify x)).trans (congrArg Subtype.val (identify.symm_apply_apply x))
  let a : T.Edge e := ⟨T.vertex e, left_mem_segment ℝ _ _⟩
  let b : T.Edge e := ⟨T.vertex (Triangle.next e), right_mem_segment ℝ _ _⟩
  have different : (identify a).val ≠ (identify b).val := by
    intro equal
    exact T.edge_endpoints_ne e (congrArg Subtype.val (identify.injective (Subtype.ext equal)))
  have enda : (identify a).val = U.vertex f ∨ (identify a).val = U.vertex (Triangle.next f) :=
    segment_isometry_maps_endpoint identify a (Or.inl rfl)
  have endb : (identify b).val = U.vertex f ∨ (identify b).val = U.vertex (Triangle.next f) :=
    segment_isometry_maps_endpoint identify b (Or.inr rfl)
  have source_area : orient (identify a).val (identify b).val (U.opposite f) ≠ 0 := by
    rcases enda with ha | ha <;> rcases endb with hb | hb
    · exact (different (ha.trans hb.symm)).elim
    · simpa only [ha, hb] using U.orient_edge_ne_zero f
    · rw [ha, hb, orient_swap]
      exact neg_ne_zero.mpr (U.orient_edge_ne_zero f)
    · exact (different (ha.trans hb.symm)).elim
  have right_area : orient (T.vertex e) (T.vertex (Triangle.next e)) (F (U.opposite f)) ≠ 0 := by
    have nonzero := orient_map_ne_zero F source_area
    rw [joined a, joined b] at nonzero
    exact nonzero
  let area := orient (T.vertex e) (T.vertex (Triangle.next e)) (T.opposite e)
  let right := orient (T.vertex e) (T.vertex (Triangle.next e)) (F (U.opposite f))
  by_cases opened : area * right < 0
  · exact ⟨⟨F, joined, opened⟩⟩
  · have positive : 0 < area * right :=
      lt_of_le_of_ne (le_of_not_gt opened) (mul_ne_zero (T.orient_edge_ne_zero e) right_area).symm
    let reflection := lineReflection (T.vertex e) (T.vertex (Triangle.next e))
    refine ⟨⟨F.trans reflection, ?_, ?_⟩⟩
    · intro x
      change reflection (F (identify x).val) = x.val
      rw [joined]
      exact lineReflection_of_mem_segment x.property
    · change area * orient (T.vertex e) (T.vertex (Triangle.next e))
        (lineReflection (T.vertex e) (T.vertex (Triangle.next e)) (F (U.opposite f))) < 0
      rw [orient_lineReflection, mul_neg]
      exact neg_lt_zero.mpr positive

/-- Choose an outward placement after proving its existence from the edge isometry. -/
def hingePlacement (T U : Triangle) (e f : Fin 3) (identify : T.Edge e ≃ᵢ U.Edge f) :
    HingePlacement T U e f identify := Classical.choice (exists_hingePlacement T U e f identify)

end Unfoldings
