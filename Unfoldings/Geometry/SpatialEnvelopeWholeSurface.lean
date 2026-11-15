module

public import Unfoldings.Geometry.SpatialEnvelope

/-! Finite closed convex cells cover the entire unbounded physical roof surface. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope

variable {I : Type*} [Fintype I] [Nonempty I] (family : I → SpatialPlane)

/-- The complete physical graph, without a horizontal truncation. -/
def wholeSurface : Set Space := Set.range (point family)

/-- The entire active portion of one actual rigid supporting plane. -/
def wholeCell (i : I) : Set Space :=
  (family i).place '' ((family i).project.symm ''
    AffineEnvelope.cell (fun j => (family j).height) i)

omit [Fintype I] [Nonempty I] in
theorem isClosed_wholeCell (i : I) : IsClosed (wholeCell family i) :=
  (family i).place.isometry.isClosedEmbedding.isClosedMap _
    ((family i).project.symm.toContinuousAffineEquiv.toHomeomorph.isClosedMap _
      (AffineEnvelope.isClosed_cell _ i))

omit [Fintype I] [Nonempty I] in
theorem convex_wholeCell (i : I) : Convex ℝ (wholeCell family i) :=
  Convex.affine_image (family i).place.toAffineMap
    (Convex.affine_image (family i).project.symm.toAffineMap (AffineEnvelope.convex_cell _ i))

/-- All original unbounded active plane pieces are retained in the exact physical graph. -/
theorem wholeSurface_eq_iUnion_cells : wholeSurface family = ⋃ i, wholeCell family i := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨i, active⟩ := AffineEnvelope.exists_height_eq (fun j => (family j).height) p
    refine Set.mem_iUnion.mpr ⟨i, (family i).project.symm p,
      ⟨p, (AffineEnvelope.mem_cell_iff _ i p).mpr active, rfl⟩, ?_⟩
    exact (point_eq_place family i active).symm
  · intro member
    obtain ⟨i, x, ⟨p, active, rfl⟩, rfl⟩ := Set.mem_iUnion.mp member
    exact ⟨p, point_eq_place family i ((AffineEnvelope.mem_cell_iff _ i p).mp active)⟩

/-- Horizontal projection is a homeomorphism of the whole physical roof onto the plane. -/
def wholeSurfaceHomeomorph : wholeSurface family ≃ₜ Plane where
  toFun z := Cap.horizontal z.val
  invFun p := ⟨point family p, Set.mem_range_self p⟩
  left_inv z := by
    obtain ⟨z, p, rfl⟩ := z
    apply Subtype.ext
    change point family (Cap.horizontal (point family p)) = point family p
    rw [horizontal_point]
  right_inv := horizontal_point family
  continuous_toFun := Cap.horizontalCLM.continuous.comp continuous_subtype_val
  continuous_invFun := (continuous_point family).subtype_mk _

end Unfoldings.SpatialEnvelope
