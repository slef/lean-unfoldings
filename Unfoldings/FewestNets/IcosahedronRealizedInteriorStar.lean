module

public import Unfoldings.FewestNets.IcosahedronRealizedStar
public import Unfoldings.FewestNets.IcosahedronInteriorStarCoverage

/-! Realize the whole cyclic star at every interior lattice site. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open MeshStar NormedSpace

theorem nonempty_interiorStarRealization {q i j : ℕ} (hq : 0 < q) (f : Fin 20)
    (hi : 0 < i) (hj : 0 < j) (sum : i + j < q) :
    Nonempty (MeshStarRealization (interiorStarSite f hi hj sum) (modelInteriorStar q i j)) := by
  let M := modelInteriorStar q i j
  obtain ⟨L, vertex⟩ := exists_modelFace_isometry f
  let t (a : Fin 6) : MeshFace q := (f, faceStarCell hi hj sum a)
  let p (a : Fin 6) := Equiv.ofBijective (faceStarCornerIndex a)
    (faceStarCornerIndex_bijective a)
  have corner_eq (a : Fin 6) (b : Fin 3) :
      inscribedCorners (t a) (p a b) =
        L ((![M.direction, M.neighborDirection a,
          M.neighborDirection (a + 1)] : Fin 3 → Space) b) := by
      rw [← map_normalize_modelGridCorners (t a) L vertex]
      congr 1
      change NormedSpace.normalize
        (modelGridCorners (faceStarCell hi hj sum a) (faceStarCornerIndex a b)) = _
      rw [modelGridCorners_faceStarCell hi hj sum]
      fin_cases b <;> rfl
  have injective : Function.Injective t :=
    fun _ _ h => faceStarCell_injective hi hj sum (congrArg Prod.snd h)
  have center : L M.direction = (interiorStarSite f hi hj sum : Space) := (corner_eq 0 0).symm
  have complete (f' : MeshFace q)
      (mem : (interiorStarSite f hi hj sum : Space) ∈ Set.range (inscribedCorners f')) :
      f' ∈ Set.range t := by
    obtain ⟨a, eq⟩ := exists_faceStarCell_eq_of_mem_corners hq f hi hj sum f' mem
    exact ⟨a, eq.symm⟩
  exact ⟨⟨L, ⟨t, injective⟩, p, center, corner_eq, complete⟩⟩

end Unfoldings.FewestNets.Icosahedron
