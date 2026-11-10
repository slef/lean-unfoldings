module

public import Unfoldings.Cap.Basic
public import Unfoldings.Cap.VerticalFrame

/-! Geometric cap inputs are preserved by any horizontal orthogonal change of frame. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Rotate or reflect every actual spatial placement while keeping height fixed. -/
def reframeFolding (L : Plane ≃ₗᵢ[ℝ] Plane) : SpatialFolding C where
  place f := (Cap.verticalFrame L).toAffineIsometryEquiv.toAffineIsometry.comp (K.folding.place f)
  joined s x := congrArg (Cap.verticalFrame L) (K.folding.joined s x)

theorem reframe_toSpace (L : Plane ≃ₗᵢ[ℝ] Plane) (retain : Set C.Seam)
    (x : C.Realization retain) :
    (K.reframeFolding L).toSpace retain x = Cap.verticalFrame L (K.folding.toSpace retain x) := by
  obtain ⟨⟨f, x⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) x
  rfl

theorem reframe_surface (L : Plane ≃ₗᵢ[ℝ] Plane) :
    (K.reframeFolding L).surface = Cap.verticalFrame L '' K.folding.surface := by
  ext z
  constructor
  · intro present
    obtain ⟨f, x, carrier, rfl⟩ := Set.mem_iUnion.mp present
    exact ⟨K.folding.place f x, Set.mem_iUnion.mpr ⟨f, x, carrier, rfl⟩, rfl⟩
  · rintro ⟨z, present, rfl⟩
    obtain ⟨f, x, carrier, rfl⟩ := Set.mem_iUnion.mp present
    exact Set.mem_iUnion.mpr ⟨f, x, carrier, rfl⟩

theorem reframe_footprint (L : Plane ≃ₗᵢ[ℝ] Plane) :
    Cap.horizontal '' (K.reframeFolding L).surface = L '' K.footprint := by
  rw [K.reframe_surface, Set.image_image, footprint, Set.image_image]
  congr 1
  funext z
  exact Cap.horizontal_verticalFrame L z

/-- The transformed cap has the same intrinsic triangles and original seams. -/
def reframe (L : Plane ≃ₗᵢ[ℝ] Plane) : ConvexCap C where
  folding := K.reframeFolding L
  normal f := Cap.verticalFrame L (K.normal f)
  normal_unit f := (Cap.verticalFrame L).norm_map _ |>.trans (K.normal_unit f)
  normal_upward f := by rw [Cap.height_verticalFrame]; exact K.normal_upward f
  normal_tangent f x := by
    change inner ℝ (Cap.verticalFrame L (K.normal f))
      (Cap.verticalFrame L ((K.folding.place f).linear x)) = 0
    rw [(Cap.verticalFrame L).inner_map_map]
    exact K.normal_tangent f x
  supporting f g x := by
    change inner ℝ (Cap.verticalFrame L (K.normal f))
      (Cap.verticalFrame L (K.folding.place g x.val) -
        Cap.verticalFrame L (K.folding.place f 0)) ≤ 0
    rw [← map_sub, (Cap.verticalFrame L).inner_map_map]
    exact K.supporting f g x
  projection_injective x y equal := by
    change Cap.horizontal ((K.reframeFolding L).toSpace Set.univ x) =
      Cap.horizontal ((K.reframeFolding L).toSpace Set.univ y) at equal
    rw [K.reframe_toSpace, K.reframe_toSpace,
      Cap.horizontal_verticalFrame, Cap.horizontal_verticalFrame] at equal
    exact K.projection_injective (L.injective equal)
  convex_projection := by
    rw [K.reframe_footprint]
    exact K.convex_projection.linear_image L.toLinearMap
  interior_projection := by
    rw [K.reframe_footprint]
    change (interior (L.toHomeomorph '' K.footprint)).Nonempty
    rw [← L.toHomeomorph.image_interior]
    exact K.interior_projection.image L
  rim_horizontal bank x := by
    change Cap.verticalFrame L (K.folding.place bank.val.face x.val) 2 = 0
    rw [Cap.height_verticalFrame]
    exact K.rim_horizontal bank x
  corners_above f i := by
    change 0 ≤ Cap.verticalFrame L (K.folding.place f ((C.triangle f).vertex i)) 2
    rw [Cap.height_verticalFrame]
    exact K.corners_above f i

@[simp] theorem reframe_tiltBound_iff (L : Plane ≃ₗᵢ[ℝ] Plane) (φ : ℝ) :
    (K.reframe L).TiltBound φ ↔ K.TiltBound φ := by
  simp only [TiltBound, reframe, Cap.height_verticalFrame]

end Unfoldings.ConvexCap
