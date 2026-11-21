module

public import Unfoldings.FewestNets.IcosahedronSiteWeights
public import Unfoldings.FewestNets.IcosahedronRealizedInteriorStar
public import Unfoldings.FewestNets.IcosahedronRealizedSeamStar
public import Unfoldings.FewestNets.IcosahedronRealizedVertexStar
public import Unfoldings.FewestNets.FiniteMeshKeys

/-! Every actual mesh site has one of the canonical face, seam, or pentagon stars. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open MeshStar
open scoped BigOperators

set_option maxHeartbeats 750000 in
-- Unfold the three exact reference weights in each of the barycentric cases.
/-- The canonical orbit representatives cover all actual cyclic Voronoi stars. -/
theorem meshSite_has_realizedModel {q : ℕ} (hq : 0 < q) (a : meshSites q) :
    (∃ i j, (i, j) ∈ faceMeshKeys q ∧ Nonempty (MeshStarRealization a (face q i j))) ∨
      (∃ i, i ∈ seamMeshKeys q ∧ Nonempty (MeshStarRealization a (seam q i))) ∨
      Nonempty (MeshStarRealization a (pentagon q)) := by
  obtain ⟨⟨t, k⟩, eq⟩ := a.property
  have eq_a : a = siteOfCorner t k := Subtype.ext eq.symm
  rw [eq_a]
  let w := localGridWeights t.2 k
  let σ := Tuple.sort w
  let x := w (σ 0)
  let y := w (σ 1)
  let z := w (σ 2)
  have sort := Tuple.monotone_sort w
  have xy : x ≤ y := sort (by decide : (0 : Fin 3) ≤ 1)
  have yz : y ≤ z := sort (by decide : (1 : Fin 3) ≤ 2)
  have total : x + y + z = q := by
    have h := (Equiv.sum_comp σ w).trans (sum_localGridWeights t.2 k)
    rwa [Fin.sum_univ_three] at h
  have zpos : 0 < z := by omega
  by_cases xpos : 0 < x
  · left
    have ypos : 0 < y := xpos.trans_le xy
    have sum : y + z < q := by omega
    let t₀ : MeshFace q := (0, faceStarCell ypos zpos sum 0)
    obtain ⟨S, sf, sc⟩ := MacroMeshSymmetry.exists_ordered t.1 σ
    have weights (d : Fin 3) :
        localGridWeights t₀.2 0 d = w (S.corner t₀.1 d) := by
      change localGridWeights (faceStarCell ypos zpos sum 0) 0 d = w (S.corner 0 d)
      rw [localGridWeights_faceStarCell_zero, sc]
      fin_cases d
      · change q - (y + z) = x
        omega
      · rfl
      · rfl
    have site := S.meshSiteEquiv_siteOfCorner_eq_of_localGridWeights hq t₀ t 0 k sf weights
    obtain ⟨R⟩ := nonempty_interiorStarRealization hq 0 ypos zpos sum
    have candidate := S.mapStar hq R
    have first_site : S.meshSiteEquiv hq (interiorStarSite 0 ypos zpos sum) = siteOfCorner t k :=
      site
    have last_weight : q - y - z = x := by omega
    have model := modelInteriorStar_eq_face sum
    rw [last_weight] at model
    exact ⟨y, x, mem_faceMeshKeys.mpr ⟨xpos, xy, by omega⟩, ⟨first_site ▸ model ▸ candidate⟩⟩
  have xzero : x = 0 := by omega
  by_cases ypos : 0 < y
  · right
    left
    have zsmall : z < q := by omega
    let c := (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 0 2)
    let ρ := c.trans σ
    let t₀ : MeshFace q := (0, seamBaseCell zpos zsmall 0)
    obtain ⟨S, sf, sc⟩ := MacroMeshSymmetry.exists_ordered t.1 ρ
    have weights (d : Fin 3) :
        localGridWeights t₀.2 0 d = w (S.corner t₀.1 d) := by
      change localGridWeights (seamBaseCell zpos zsmall 0) 0 d = w (S.corner 0 d)
      rw [localGridWeights_seamBaseCell_zero, sc]
      fin_cases d
      · change q - z = y
        omega
      · rfl
      · exact xzero.symm
    have site := S.meshSiteEquiv_siteOfCorner_eq_of_localGridWeights hq t₀ t 0 k sf weights
    obtain ⟨R⟩ := nonempty_referenceSeamStarRealization hq zpos zsmall
    have first_site : S.meshSiteEquiv hq (referenceSeamSite zpos zsmall) = siteOfCorner t k := site
    exact ⟨z, mem_seamMeshKeys.mpr ⟨by omega, zsmall⟩, ⟨first_site ▸ S.mapStar hq R⟩⟩
  right
  right
  have yzero : y = 0 := by omega
  let ρ := (Equiv.swap (0 : Fin 3) 2).trans σ
  let t₀ := referenceVertexFineFace hq 0
  obtain ⟨S, sf, sc⟩ := MacroMeshSymmetry.exists_ordered t.1 ρ
  have weights (d : Fin 3) :
      localGridWeights t₀.2 0 d = w (S.corner t₀.1 d) := by
    change localGridWeights (referenceVertexCell hq) 0 d = w (S.corner 0 d)
    rw [localGridWeights_referenceVertexCell, sc]
    fin_cases d
    · change q = z
      omega
    · exact yzero.symm
    · exact xzero.symm
  have site := S.meshSiteEquiv_siteOfCorner_eq_of_localGridWeights hq t₀ t 0 k sf weights
  obtain ⟨R⟩ := nonempty_referenceVertexStarRealization hq
  have first_site : S.meshSiteEquiv hq (referenceVertexSite hq) = siteOfCorner t k := site
  exact ⟨first_site ▸ S.mapStar hq R⟩

end Unfoldings.FewestNets.Icosahedron
