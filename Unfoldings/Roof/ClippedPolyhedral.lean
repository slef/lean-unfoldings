module

public import Unfoldings.Convex.FiniteClippedExtension
public import Unfoldings.Convex.FiniteDualVertices
public import Unfoldings.Roof.ClippedStrictRegion

/-! Finite polyhedral structure and exact normal cells of the actual clipped roof extension. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem exists_finite_clippedExtension {J : Type u} [Fintype J] [Nonempty J]
    (domain : J → Plane →ᵃ[ℝ] ℝ) {Z : ℝ}
    (compact : IsCompact (AffineEnvelope.clip domain Z)) {q : Plane}
    (higher : Z < AffineEnvelope.height domain q) :
    ∃ (vertices : Finset Plane) (nonempty : vertices.Nonempty),
      (∀ p ∈ vertices, p ∈ AffineEnvelope.clip domain Z) ∧
      ∀ x : Plane,
        (K.clippedExtension (AffineEnvelope.clip domain Z) compact ⟨q, higher.le⟩).height x =
          vertices.sup' nonempty (fun p => inner ℝ x p - K.dualCost p) := by
  let := K.nonempty_face
  exact FiniteDual.exists_finite_clipped_extension K.dualPoint K.dualLevel domain compact higher

/-- Full two-dimensional normal cells of the extension occur at original lifted corners. -/
theorem clippedExtension_full_normal_cell_original_corner {slopes : Set Plane}
    (compact : IsCompact slopes) (nonempty : slopes.Nonempty) (x : Plane)
    (full : (interior {p | (K.clippedExtension slopes compact nonempty).Active x p}).Nonempty) :
    ∃ corner : Face × Fin 3, K.dualPoint corner = x ∧
      (K.clippedExtension slopes compact nonempty).height x = K.dualLevel corner := by
  let := K.nonempty_face
  exact FiniteDual.active_cell_interior_original_vertex K.dualPoint K.dualLevel compact nonempty
    x full

/-- Every surviving original normal cell is exactly its intersection with the slope polygon. -/
theorem clippedExtension_normal_cell_eq {slopes : Set Plane}
    (compact : IsCompact slopes) (nonempty : slopes.Nonempty) {x : Plane}
    (member : x ∈ K.footprint) (survives : (slopes ∩ K.primalNormalCell x).Nonempty) :
    {p | (K.clippedExtension slopes compact nonempty).Active x p} =
      slopes ∩ K.primalNormalCell x := by
  obtain ⟨p, selected, normal⟩ := survives
  have height := K.clippedExtension_eq_original_of_normal compact nonempty member normal selected
  ext q
  exact K.clippedExtension_active_iff_original compact nonempty member height

end Unfoldings.ConvexRoof
