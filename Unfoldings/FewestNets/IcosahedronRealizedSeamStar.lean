module

public import Unfoldings.FewestNets.IcosahedronReferenceSeamStar

/-! The canonical reflected seam star realizes an actual cyclic fine mesh star. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open MeshStar NormedSpace

def seamMirrorIndex : Fin 3 → Fin 6 := ![5, 4, 3]

private theorem seamReflection_stepU (q : ℕ) : seamReflection (stepU q) = stepU q := by
  rw [stepU, map_smul, map_sub, seamReflection_cornerB, seamReflection_cornerA]

private theorem seamReflection_site (q i : ℕ) :
    seamReflection (seam q i).site = (seam q i).site := by
  change seamReflection (cornerA + (i : ℝ) • stepU q) = _
  rw [map_add, map_smul, seamReflection_cornerA, seamReflection_stepU]
  rfl

/-- Read the reflected triangles in reverse order to keep the cyclic neighbor order. -/
theorem modelGridCorners_seamMirror {q i : ℕ} (hi : 0 < i) (last : i < q) (k l : Fin 3) :
    seamReflection (modelGridCorners (seamBaseCell hi last k)
      (seamBaseCornerIndex k (Equiv.swap 1 2 l))) =
      (![(seam q i).site, (seam q i).neighbor (seamMirrorIndex k),
        (seam q i).neighbor (seamMirrorIndex k + 1)] : Fin 3 → Space) l := by
  rw [modelGridCorners_seamBaseCell hi last]
  let z := (seam q i).site
  change seamReflection
      ((![z, seamNeighbor q z (seamBaseIndex k), seamNeighbor q z (seamBaseIndex k + 1)]
        : Fin 3 → Space) (Equiv.swap 1 2 l)) =
    (![z, seamNeighbor q z (seamMirrorIndex k), seamNeighbor q z (seamMirrorIndex k + 1)]
      : Fin 3 → Space) l
  have fixed : seamReflection z = z := seamReflection_site q i
  fin_cases k <;> fin_cases l <;>
    simp [seamBaseIndex, seamMirrorIndex, seamNeighbor, Equiv.swap_apply_def, Fin.add_def, fixed]
  all_goals simp only [← seamReflection_apply, map_add, map_sub, fixed, seamReflection_stepU]

def referenceSeamCornerOrder (k : Fin 6) : Equiv.Perm (Fin 3) :=
  let label := referenceSeamLabel k
  let p := Equiv.ofBijective (seamBaseCornerIndex label.2)
    (seamBaseCornerIndex_bijective label.2)
  if label.1 then ((Equiv.swap 1 2).trans p).trans referenceSeamOrder else p

/-- All six triangles around the seam representative have the stated reflected coordinates. -/
theorem nonempty_referenceSeamStarRealization {q i : ℕ} (hq : 0 < q)
    (hi : 0 < i) (last : i < q) :
    Nonempty (MeshStarRealization (referenceSeamSite hi last) (seam q i)) := by
  obtain ⟨L, baseFrame, mirrorFrame⟩ := exists_referenceSeam_frame
  let M := seam q i
  let t := referenceSeamFace hi last
  let p := referenceSeamCornerOrder
  have base (u l : Fin 3) :
      inscribedCorners (0, seamBaseCell hi last u) (seamBaseCornerIndex u l) =
        L ((![M.direction, M.neighborDirection (seamBaseIndex u),
          M.neighborDirection (seamBaseIndex u + 1)] : Fin 3 → Space) l) := by
    rw [← map_normalize_modelGridCorners (0, seamBaseCell hi last u) L baseFrame]
    congr 1
    change normalize (modelGridCorners (seamBaseCell hi last u) (seamBaseCornerIndex u l)) = _
    rw [modelGridCorners_seamBaseCell hi last]
    fin_cases l <;> rfl
  have mirror (u l : Fin 3) :
      inscribedCorners (2, permuteGridCell referenceSeamOrder (seamBaseCell hi last u))
        (referenceSeamOrder (seamBaseCornerIndex u (Equiv.swap 1 2 l))) =
          L ((![M.direction, M.neighborDirection (seamMirrorIndex u),
            M.neighborDirection (seamMirrorIndex u + 1)] : Fin 3 → Space) l) := by
    rw [← map_normalize_modelGridCorners_permute hq 2 referenceSeamOrder _ _ mirrorFrame]
    apply congrArg L
    have moved (x : Space) : seamReflection (normalize x) = normalize (seamReflection x) := by
      simp only [NormedSpace.normalize, map_smul, LinearIsometryEquiv.norm_map]
    change seamReflection
      (normalize (modelGridCorners (seamBaseCell hi last u)
        (seamBaseCornerIndex u (Equiv.swap 1 2 l)))) = _
    rw [moved, modelGridCorners_seamMirror hi last]
    fin_cases l <;> rfl
  have corner_eq (k : Fin 6) (l : Fin 3) :
      inscribedCorners (t k) (p k l) =
        L ((![M.direction, M.neighborDirection k, M.neighborDirection (k + 1)]
          : Fin 3 → Space) l) := by
    fin_cases k
    · exact base 0 l
    · exact base 1 l
    · exact base 2 l
    · exact mirror 2 l
    · exact mirror 1 l
    · exact mirror 0 l
  refine ⟨⟨L, ⟨t, referenceSeamFace_injective hi last⟩, p, (corner_eq 0 0).symm,
    corner_eq, fun s mem => ?_⟩⟩
  exact exists_referenceSeamFace_eq_of_mem_corners hq hi last s mem

end Unfoldings.FewestNets.Icosahedron
