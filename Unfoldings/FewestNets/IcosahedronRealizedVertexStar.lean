module

public import Unfoldings.FewestNets.IcosahedronReferenceVertexStar

/-! The pentagon model realizes the five actual fine triangles at an original vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open MeshStar NormedSpace

private theorem chordCorners_referenceVertexFineFace {q : ℕ} (hq : 0 < q) (k : Fin 5)
    (l : Fin 3) :
    let p (j : Fin 5) := rawVertex 0 +
      (q : ℝ)⁻¹ • (rawVertex (referenceVertexNeighbor j) - rawVertex 0)
    chordCorners (referenceVertexFineFace hq k) l =
      (![rawVertex 0, p k, p (k + 1)] : Fin 3 → Space) l := by
  dsimp only [chordCorners, referenceVertexFineFace, referenceVertexCell, faceCorners]
  rw [referenceVertexFace_corners]
  fin_cases l <;> simp [TriangleGrid.cellCorners, TriangleGrid.corner, TriangleGrid.point,
    div_eq_inv_mul]

theorem nonempty_referenceVertexStarRealization {q : ℕ} (hq : 0 < q) :
    Nonempty (MeshStarRealization (referenceVertexSite hq) (pentagon q)) := by
  obtain ⟨L, he⟩ := exists_modelFace_isometry 0
  let M := pentagon q
  let t := referenceVertexFineFace hq
  have rotate (x : Space) : L (normalize x) = normalize (L x) := by
    simp only [NormedSpace.normalize, map_smul, LinearIsometryEquiv.norm_map]
  have center : L M.site = radius⁻¹ • rawVertex 0 := he 0
  have corner_eq (k : Fin 5) (l : Fin 3) :
      inscribedCorners (t k) l =
        L ((![M.direction, M.neighborDirection k, M.neighborDirection (k + 1)] : Fin 3 → Space) l)
      := by
    have remove (x : Space) : normalize (radius⁻¹ • x) = normalize x :=
      normalize_smul_of_pos (inv_pos.mpr radius_pos) x
    rw [inscribedCorners, chordCorners_referenceVertexFineFace hq k l]
    fin_cases l
    · change normalize (rawVertex 0) = L (normalize M.site)
      rw [rotate, center, remove]
    · change normalize (rawVertex 0 + (q : ℝ)⁻¹ •
          (rawVertex (referenceVertexNeighbor k) - rawVertex 0)) = L (normalize (M.neighbor k))
      rw [rotate, map_pentagon_neighbor L he k, remove]
    · change normalize (rawVertex 0 + (q : ℝ)⁻¹ •
          (rawVertex (referenceVertexNeighbor (k + 1)) - rawVertex 0)) =
        L (normalize (M.neighbor (k + 1)))
      rw [rotate, map_pentagon_neighbor L he (k + 1), remove]
  have inj : Function.Injective t :=
    fun _ _ h => referenceVertexFace_injective (congrArg Prod.fst h)
  exact ⟨⟨L, ⟨t, inj⟩, fun _ => Equiv.refl _, (corner_eq 0 0).symm,
    corner_eq, exists_referenceVertexFineFace_eq_of_mem_corners hq⟩⟩

end Unfoldings.FewestNets.Icosahedron
