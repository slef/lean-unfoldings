module

public import Unfoldings.Roof.ClippedPolyhedral
public import Unfoldings.Convex.PhysicalModelMesh

/-! Construct physical clipped roof models and locate their actual positive curvature. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The finite physical model is constructed from the original roof vertices and the
actual clipping polygon. Its support planes have the exact original dual intercepts. -/
def clippedPhysicalModel {J : Type u} [Fintype J] [Nonempty J]
    (domain : J → Plane →ᵃ[ℝ] ℝ) {Z : ℝ}
    (compact : IsCompact (AffineEnvelope.clip domain Z)) {q : Plane}
    (higher : Z < AffineEnvelope.height domain q) :
    (K.clippedExtension (AffineEnvelope.clip domain Z) compact ⟨q, higher.le⟩).FiniteSlopeModel :=
  Classical.choice (by
    obtain ⟨vertices, nonempty, contained, realizes⟩ :=
      K.exists_finite_clippedExtension domain compact higher
    exact ⟨⟨vertices, nonempty, contained, realizes⟩⟩)

variable {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
  {Z : ℝ} (T : SpatialEnvelope.Triangulation M.plane Z)
  (conforming : TriangleFamily.Conforming T.projectedTriangle)
  (inside : (interior (SpatialEnvelope.clip M.plane Z)).Nonempty)

local instance : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- Every positive intrinsic curvature vertex in the constructed physical extension is an
original lifted roof corner. Auxiliary meshing adds no curvature, at any normal tilt. -/
theorem clippedPhysical_positive_curvature_original_corner (convex : Convex ℝ slopes)
    (v : T.pairedComplex.Vertex Set.univ)
    (curved : 0 < T.pairedComplex.interiorAngularDefect Set.univ v) :
    ∃ corner : Face × Fin 3,
      K.dualPoint corner = (T.roof conforming inside).projectedVertex v ∧
      (K.clippedExtension slopes compact nonempty).height
        ((T.roof conforming inside).projectedVertex v) = K.dualLevel corner := by
  let := K.nonempty_face
  have full := M.active_cell_interior_of_positive_curvature T conforming inside convex
    (FiniteDual.convex_cost K.dualPoint K.dualLevel) v curved
  exact K.clippedExtension_full_normal_cell_original_corner compact nonempty _ full

end Unfoldings.ConvexRoof
