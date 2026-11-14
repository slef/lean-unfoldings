module

public import Unfoldings.Roof.ClippedExtension
public import Unfoldings.Convex.BoundaryPotential

/-! Safe exterior rays avoid every closed selected original triangle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem clippedExtension_ray_avoids_selected_faces {slopes : Set Plane}
    (compact : IsCompact slopes) (nonempty : slopes.Nonempty) {p v u : Plane} {c t : ℝ}
    (active : (K.clippedExtension slopes compact nonempty).Active v p)
    (side : inner ℝ u p = c) (support : ∀ q ∈ slopes, inner ℝ u q ≤ c)
    (direction : u ≠ 0) (time : 0 < t) (f : Face)
    (selected : K.normalSlope f ∈ interior slopes) :
    v + t • u ∉ (K.projectedTriangle f).carrier := by
  intro member
  have along := K.clippedExtension_original_face_active compact nonempty f
    (interior_subset selected) member
  exact (K.clippedExtension slopes compact nonempty).active_ray_not_interior
    active side support direction time along selected

end Unfoldings.ConvexRoof
