module

public import Unfoldings.FewestNets.IcosahedronSeamStarGrid
public import Unfoldings.FewestNets.IcosahedronSeamFrame
public import Unfoldings.FewestNets.IcosahedronFineSymmetry

/-! The six actual fine triangles around a site of the reference macroedge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open MeshStar

/-- The reference macroedge orders the first three triangles and then
the reflected triangles in reverse. -/
def referenceSeamLabel (k : Fin 6) : Bool × Fin 3 :=
  ![(false, 0), (false, 1), (false, 2), (true, 2), (true, 1), (true, 0)] k

theorem referenceSeamLabel_bijective : Function.Bijective referenceSeamLabel := by
  refine ⟨?_, ?_⟩
  · have table : ∀ i j : Fin 6, referenceSeamLabel i = referenceSeamLabel j → i = j := by
      decide +kernel
    exact table
  · rintro ⟨b, l⟩
    cases b <;> fin_cases l <;> decide +kernel

def referenceSeamFace {q i : ℕ} (hi : 0 < i) (last : i < q) (k : Fin 6) : MeshFace q :=
  let label := referenceSeamLabel k
  let cell := seamBaseCell hi last label.2
  if label.1 then (2, permuteGridCell referenceSeamOrder cell) else (0, cell)

def referenceSeamSite {q i : ℕ} (hi : 0 < i) (last : i < q) : meshSites q :=
  siteOfCorner (0, seamBaseCell hi last 0) 0

theorem referenceSeamFace_injective {q i : ℕ} (hi : 0 < i) (last : i < q) :
    Function.Injective (referenceSeamFace hi last) := by
  intro k l equal
  cases hk : (referenceSeamLabel k).1 <;> cases hl : (referenceSeamLabel l).1
  · apply referenceSeamLabel_bijective.1
    apply Prod.ext (hk.trans hl.symm)
    apply seamBaseCell_injective hi last
    simpa only [referenceSeamFace, hk, hl, Bool.false_eq_true, ite_false]
      using congrArg Prod.snd equal
  · have h := congrArg Prod.fst equal
    simp [referenceSeamFace, hk, hl] at h
  · have h := congrArg Prod.fst equal
    simp [referenceSeamFace, hk, hl] at h
  · apply referenceSeamLabel_bijective.1
    apply Prod.ext (hk.trans hl.symm)
    apply seamBaseCell_injective hi last
    apply permuteGridCell_injective referenceSeamOrder
    simpa only [referenceSeamFace, hk, hl, ite_true] using congrArg Prod.snd equal

theorem referenceSeamSite_gridWeights {q i : ℕ} (hi : 0 < i) (last : i < q) :
    gridWeights (0, seamBaseCell hi last 0) 0 = extendFaceWeights 0 ![q - i, i, 0] := by
  rw [gridWeights, localGridWeights_seamBaseCell_zero hi last]

/-- Every fine triangle containing the reference seam site occurs in the cyclic list. -/
theorem exists_referenceSeamFace_eq_of_mem_corners {q i : ℕ} (hq : 0 < q)
    (hi : 0 < i) (last : i < q) (t : MeshFace q)
    (mem : (referenceSeamSite hi last : Space) ∈ Set.range (inscribedCorners t)) :
    ∃ k : Fin 6, referenceSeamFace hi last k = t := by
  obtain ⟨j, eq⟩ := mem
  have same := (gridWeights_eq_of_inscribedCorners_eq hq t (0, seamBaseCell hi last 0) j 0 eq).trans
    (referenceSeamSite_gridWeights hi last)
  have atA : gridWeights t j 0 = q - i := by
    rw [same, ← show faceVertex 0 0 = (0 : Fin 12) by decide, extendFaceWeights_faceVertex]
    rfl
  have atB : gridWeights t j 4 = i := by
    rw [same, ← show faceVertex 0 1 = (4 : Fin 12) by decide, extendFaceWeights_faceVertex]
    rfl
  have present {v : Fin 12} (positive : 0 < gridWeights t j v) :
      v ∈ Set.range (faceVertex t.1) := by
    by_contra absent
    rw [gridWeights, extendFaceWeights_zero_of_outside _ _ absent] at positive
    omega
  have zero {v : Fin 12} (absent : v ∉ Set.range (faceVertex 0)) : gridWeights t j v = 0 :=
    congrFun same v |>.trans (extendFaceWeights_zero_of_outside _ _ absent)
  have coeff (d : Fin 3) : localGridWeights t.2 j d = gridWeights t j (faceVertex t.1 d) :=
    (extendFaceWeights_faceVertex t.1 _ d).symm
  rcases (referenceSeam_macroface_iff t.1).mp
    ⟨present (atA ▸ Nat.sub_pos_of_lt last), present (atB ▸ hi)⟩ with base | mirror
  · have first : localGridWeights t.2 j 1 = i := by
      rw [coeff, base]
      exact atB
    have second : localGridWeights t.2 j 2 = 0 := by
      rw [coeff, base, same, extendFaceWeights_faceVertex]
      rfl
    obtain ⟨l, cell⟩ := exists_seamBaseCell_of_weights hi last t.2 j first second
    obtain ⟨k, label⟩ := referenceSeamLabel_bijective.2 (false, l)
    exact ⟨k, by rw [referenceSeamFace, label]; exact (Prod.ext base cell).symm⟩
  · let σ := referenceSeamOrder
    let s := permuteGridCell σ.symm t.2
    have first : localGridWeights s (σ.symm j) 1 = i := by
      rw [show (1 : Fin 3) = σ.symm 2 by decide, localGridWeights_permuteGridCell, coeff, mirror]
      exact atB
    have second : localGridWeights s (σ.symm j) 2 = 0 := by
      rw [show (2 : Fin 3) = σ.symm 1 by decide, localGridWeights_permuteGridCell, coeff, mirror]
      exact zero (by decide : (8 : Fin 12) ∉ Set.range (faceVertex 0))
    obtain ⟨l, cell⟩ := exists_seamBaseCell_of_weights hi last s (σ.symm j) first second
    obtain ⟨k, label⟩ := referenceSeamLabel_bijective.2 (true, l)
    refine ⟨k, ?_⟩
    rw [referenceSeamFace, label]
    apply Prod.ext mirror.symm
    have inverse : permuteGridCell σ s = t.2 :=
      by simpa only [Equiv.symm_symm] using permuteGridCell_inverse σ.symm t.2
    exact (congrArg (permuteGridCell σ) cell).symm.trans inverse

end Unfoldings.FewestNets.Icosahedron
