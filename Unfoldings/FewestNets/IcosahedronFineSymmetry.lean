module

public import Unfoldings.FewestNets.IcosahedronGridPermutation
public import Unfoldings.FewestNets.IcosahedronMacroSymmetry
public import Unfoldings.FewestNets.IcosahedronRealizedStar

/-! Macroface symmetries induce actual fine-face and site symmetries. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

private theorem gridCell_eq_of_localGridMin_and_flag {q : ℕ} {t s : GridCell q}
    (mins : localGridMin t = localGridMin s) (flag : t.val.2.2 = s.val.2.2) : t = s :=
  Subtype.ext (Prod.ext (Fin.ext (congrFun mins 1)) (Prod.ext (Fin.ext (congrFun mins 2)) flag))

theorem localGridMin_permuteGridCell {q : ℕ} (σ : Equiv.Perm (Fin 3)) (t : GridCell q) :
    localGridMin (permuteGridCell σ t) = localGridMin t ∘ σ.symm := by
  rw [permuteGridCell, localGridMin_gridCellOfMin]

theorem permuteGridCell_inverse {q : ℕ} (σ : Equiv.Perm (Fin 3)) (t : GridCell q) :
    permuteGridCell σ.symm (permuteGridCell σ t) = t := by
  refine gridCell_eq_of_localGridMin_and_flag
    (t := permuteGridCell σ.symm (permuteGridCell σ t)) (s := t) ?_ rfl
  rw [localGridMin_permuteGridCell, localGridMin_permuteGridCell]
  funext i
  simp

theorem permuteGridCell_injective {q : ℕ} (σ : Equiv.Perm (Fin 3)) :
    Function.Injective (fun t : GridCell q => permuteGridCell σ t) := by
  intro t s eq
  have h := congrArg (permuteGridCell σ.symm) eq
  exact (permuteGridCell_inverse σ t).symm.trans (h.trans (permuteGridCell_inverse σ s))

namespace MacroMeshSymmetry

variable (S : MacroMeshSymmetry) {q : ℕ}

/-- The induced equivalence on fine triangles. -/
def meshFaceEquiv (q : ℕ) : MeshFace q ≃ MeshFace q where
  toFun t := (S.face t.1, permuteGridCell (S.corner t.1) t.2)
  invFun t := (S.face.symm t.1, permuteGridCell (S.corner (S.face.symm t.1)).symm t.2)
  left_inv t := by
    dsimp only
    rw [S.face.symm_apply_apply, permuteGridCell_inverse]
  right_inv t := by
    let σ := S.corner (S.face.symm t.1)
    change (S.face (S.face.symm t.1), permuteGridCell σ (permuteGridCell σ.symm t.2)) = t
    exact Prod.ext (S.face.apply_symm_apply t.1)
      (by simpa only [Equiv.symm_symm] using permuteGridCell_inverse σ.symm t.2)

theorem map_inscribedCorners (hq : 0 < q) (t : MeshFace q) (i : Fin 3) :
    S.frame (inscribedCorners t i) =
      inscribedCorners (S.meshFaceEquiv q t) (S.corner t.1 i) := by
  obtain ⟨L, model⟩ := exists_modelFace_isometry t.1
  have map_corner (j : Fin 3) :
      (L.trans S.frame) (modelCorners j) = unitFaceCorners (S.face t.1) (S.corner t.1 j) := by
    change S.frame (L (modelCorners j)) = _
    rw [model, unitFaceCorners, map_smul, S.faceCorners_eq]
    rfl
  rw [← map_normalize_modelGridCorners t L model i]
  exact map_normalize_modelGridCorners_permute hq _ _ t.2 (L.trans S.frame) map_corner i

theorem maps_meshSites (hq : 0 < q) {a : Space} (ha : a ∈ meshSites q) :
    S.frame a ∈ meshSites q := by
  obtain ⟨⟨t, i⟩, rfl⟩ := ha
  exact ⟨(S.meshFaceEquiv q t, S.corner t.1 i), (S.map_inscribedCorners hq t i).symm⟩

/-- The same frame permutes the radially projected grid sites. -/
def meshSiteEquiv (hq : 0 < q) : meshSites q ≃ meshSites q :=
  Equiv.ofBijective (fun a => ⟨S.frame a, S.maps_meshSites hq a.property⟩) <| by
    constructor
    · intro a b eq
      exact Subtype.ext (S.frame.injective (congrArg Subtype.val eq))
    · intro a
      obtain ⟨⟨s, j⟩, hj⟩ := a.property
      obtain ⟨t, rfl⟩ := (S.meshFaceEquiv q).surjective s
      obtain ⟨i, rfl⟩ := (S.corner t.1).surjective j
      exact ⟨siteOfCorner t i, Subtype.ext ((S.map_inscribedCorners hq t i).trans hj)⟩

theorem mem_corners_meshFaceEquiv_iff (hq : 0 < q) (t : MeshFace q) (a : meshSites q) :
    (S.meshSiteEquiv hq a : Space) ∈ Set.range (inscribedCorners (S.meshFaceEquiv q t)) ↔
      (a : Space) ∈ Set.range (inscribedCorners t) := by
  constructor
  · rintro ⟨j, eq⟩
    obtain ⟨i, rfl⟩ := (S.corner t.1).surjective j
    rw [← S.map_inscribedCorners hq t i] at eq
    exact ⟨i, S.frame.injective eq⟩
  · rintro ⟨i, eq⟩
    exact ⟨S.corner t.1 i, (S.map_inscribedCorners hq t i).symm.trans (congrArg S.frame eq)⟩

/-- Transport a complete star realization by a symmetry of the actual mesh. -/
def mapStar (hq : 0 < q) {n : ℕ} {a : meshSites q} {star : MeshStar (n + 1)}
    (R : MeshStarRealization a star) : MeshStarRealization (S.meshSiteEquiv hq a) star where
  frame := R.frame.trans S.frame
  face := R.face.trans (S.meshFaceEquiv q).toEmbedding
  index k := (R.index k).trans (S.corner (R.face k).1)
  center := congrArg S.frame R.center
  corner_eq k l :=
    (S.map_inscribedCorners hq (R.face k) (R.index k l)).symm.trans
      (congrArg S.frame (R.corner_eq k l))
  complete t mem := by
    obtain ⟨s, rfl⟩ := (S.meshFaceEquiv q).surjective t
    obtain ⟨k, hk⟩ := R.complete s ((S.mem_corners_meshFaceEquiv_iff hq s a).mp mem)
    exact ⟨k, congrArg (S.meshFaceEquiv q) hk⟩

end MacroMeshSymmetry
end Unfoldings.FewestNets.Icosahedron
