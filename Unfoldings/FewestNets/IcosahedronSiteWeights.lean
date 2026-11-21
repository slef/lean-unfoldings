module

public import Unfoldings.FewestNets.IcosahedronFineSymmetry

/-! Integer barycentric weights give exact coordinates for all actual mesh sites. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open NormedSpace
open scoped BigOperators

/-- The global barycentric weights of a site, read from any triangle that contains it. -/
def meshSiteWeights {q : ℕ} (a : meshSites q) : Fin 12 → ℕ :=
  gridWeights a.property.choose.1 a.property.choose.2

theorem meshSiteWeights_eq {q : ℕ} (hq : 0 < q) (a : meshSites q) (t : MeshFace q) (i : Fin 3)
    (same : inscribedCorners t i = (a : Space)) :
    meshSiteWeights a = gridWeights t i :=
  gridWeights_eq_of_inscribedCorners_eq hq _ t _ i (a.property.choose_spec.trans same.symm)

theorem meshSiteWeights_siteOfCorner {q : ℕ} (hq : 0 < q) (t : MeshFace q) (i : Fin 3) :
    meshSiteWeights (siteOfCorner t i) = gridWeights t i :=
  meshSiteWeights_eq hq _ t i rfl

theorem meshSiteWeights_injective {q : ℕ} (hq : 0 < q) :
    Function.Injective (meshSiteWeights (q := q)) := by
  intro a b eq
  have locate (z : meshSites q) : (z : Space) =
      normalize (∑ i, ((meshSiteWeights z i : ℝ) / q) • rawVertex i) := by
    rw [meshSiteWeights]
    have h := z.property.choose_spec
    change inscribedCorners z.property.choose.1 z.property.choose.2 = (z : Space) at h
    calc
      (z : Space) = inscribedCorners z.property.choose.1 z.property.choose.2 := h.symm
      _ = _ := by rw [inscribedCorners, chordCorners_eq_gridWeights hq]
  apply Subtype.ext
  rw [locate a, locate b, eq]

/-- Every nonnegative integer barycentric triple of total weight q occurs at a fine corner. -/
theorem exists_gridCorner_of_localGridWeights {q : ℕ} (hq : 0 < q) (w : Fin 3 → ℕ)
    (total : (∑ d, w d) = q) :
    ∃ t : GridCell q, ∃ i : Fin 3, localGridWeights t i = w := by
  classical
  have exists_pos : ∃ i, 0 < w i := by
    by_contra! none
    have zero (i : Fin 3) : w i = 0 := Nat.eq_zero_of_le_zero (none i)
    simp only [zero, Finset.sum_const_zero] at total
    omega
  obtain ⟨i, pos⟩ := exists_pos
  let δ (d : Fin 3) : ℕ := if d = i then 1 else 0
  let w₀ (d : Fin 3) := w d - δ d
  have restore (d : Fin 3) : w₀ d + δ d = w d := by
    apply Nat.sub_add_cancel
    by_cases eq : d = i
    · subst d
      rw [show δ i = 1 by simp [δ]]
      exact Nat.succ_le_of_lt pos
    · simp [δ, eq]
  have penalty : (∑ d, δ d) = 1 := by simp [δ]
  have total₀ : (∑ d, w₀ d) + 1 = q := by
    rw [← penalty, ← Finset.sum_add_distrib]
    simp only [restore, total]
  have sum : (∑ d, w₀ d) + (if false then 2 else 1) = q := total₀
  let t := gridCellOfMin false w₀ sum
  refine ⟨t, i, funext fun d => ?_⟩
  change localGridMin t d + (if (d = i) ↔ (false = false) then 1 else 0) = w d
  simpa [δ] using (congrArg (fun x => x + δ d)
    (congrFun (localGridMin_gridCellOfMin false w₀ sum) d)).trans (restore d)

namespace MacroMeshSymmetry

theorem meshSiteEquiv_siteOfCorner_eq_of_localGridWeights {q : ℕ} (S : MacroMeshSymmetry)
    (hq : 0 < q) (t s : MeshFace q) (i j : Fin 3) (same_face : S.face t.1 = s.1)
    (weights : ∀ d, localGridWeights t.2 i d = localGridWeights s.2 j (S.corner t.1 d)) :
    S.meshSiteEquiv hq (siteOfCorner t i) = siteOfCorner s j := by
  apply Subtype.ext
  change S.frame (inscribedCorners t i) = inscribedCorners s j
  rw [S.map_inscribedCorners hq t i]
  unfold inscribedCorners
  congr 1
  rw [chordCorners_eq_localGridWeights hq, chordCorners_eq_localGridWeights hq]
  apply Finset.sum_congr rfl
  intro d _
  obtain ⟨e, rfl⟩ := (S.corner t.1).surjective d
  change (((localGridWeights (permuteGridCell (S.corner t.1) t.2)
    (S.corner t.1 i) (S.corner t.1 e) : ℝ) / q) • faceCorners (S.face t.1) (S.corner t.1 e)) = _
  rw [localGridWeights_permuteGridCell, weights, same_face]

end MacroMeshSymmetry

end Unfoldings.FewestNets.Icosahedron
