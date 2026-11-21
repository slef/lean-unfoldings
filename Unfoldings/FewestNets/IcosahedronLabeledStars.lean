module

public import Unfoldings.FewestNets.IcosahedronPerimeterIndex
public import Unfoldings.FewestNets.IcosahedronRealizedInteriorStar
public import Unfoldings.FewestNets.IcosahedronRealizedSeamStar
public import Unfoldings.FewestNets.IcosahedronRealizedVertexStar

/-! The canonical model at each site retains the exact global barycentric label. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open MeshStar
open scoped BigOperators

private theorem extendFaceWeights_two (f : Fin 20) (σ : Equiv.Perm (Fin 3))
    (w : Fin 3 → ℕ) {a b : ℕ} (wa : w (σ 0) = a) (wb : w (σ 1) = b) (wc : w (σ 2) = 0) :
    extendFaceWeights f w = edgeBarycentricWeights (faceVertex f (σ 0))
      (faceVertex f (σ 1)) (a, b) := by
  funext v
  let F (d : Fin 3) := if faceVertex f d = v then w d else 0
  change (∑ d, F d) = _
  rw [← Equiv.sum_comp σ F, Fin.sum_univ_three]
  simp only [F, wa, wb, wc, ite_self, add_zero]
  have ab : faceVertex f (σ 0) ≠ faceVertex f (σ 1) :=
    (faceVertex_injective f).ne (σ.injective.ne (by decide))
  by_cases va : v = faceVertex f (σ 0)
  · simp [edgeBarycentricWeights, va, eq_comm, ab]
  · by_cases vb : v = faceVertex f (σ 1)
    · simp [edgeBarycentricWeights, vb, eq_comm, ab]
    · simp [edgeBarycentricWeights, va, vb, eq_comm]

private theorem edgeBarycentricWeights_swap {a b : Fin 12} (ab : a ≠ b) (i j : ℕ) :
    edgeBarycentricWeights a b (i, j) = edgeBarycentricWeights b a (j, i) := by
  funext v
  by_cases va : v = a
  · simp [edgeBarycentricWeights, va, ab]
  · by_cases vb : v = b
    · simp [edgeBarycentricWeights, vb, ab.symm]
    · simp [edgeBarycentricWeights, va, vb]

private theorem Adjacent.reverse {a b : Fin 12} (h : Adjacent a b) : Adjacent b a :=
  adjacent_of_inner_rawVertex_eq ((real_inner_comm (rawVertex a) (rawVertex b)).trans
    (inner_rawVertex_of_adjacent h))

set_option maxHeartbeats 900000 in
-- Unfold the three exact reference weights in each of the barycentric cases.
theorem exists_perimeterIndex_realizing {q : ℕ} (hq : 0 < q) (a : meshSites q) :
    ∃ label : PerimeterIndex q, perimeterIndexWeights label = meshSiteWeights a ∧
      perimeterIndexRealizes a label := by
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
  have site_weights : meshSiteWeights (siteOfCorner t k) = extendFaceWeights t.1 w :=
    meshSiteWeights_siteOfCorner hq t k
  have zpos : 0 < z := by omega
  by_cases xpos : 0 < x
  · have ypos : 0 < y := xpos.trans_le xy
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
    have first_site : S.meshSiteEquiv hq (interiorStarSite 0 ypos zpos sum) = siteOfCorner t k :=
      site
    have last_weight : q - y - z = x := by omega
    have model := modelInteriorStar_eq_face sum
    rw [last_weight] at model
    have key : (y, x) ∈ faceMeshKeys q := mem_faceMeshKeys.mpr ⟨xpos, xy, by omega⟩
    obtain ⟨number, at_key⟩ := List.mem_iff_get.mp key
    have sorted : w ∘ σ = ![x, y, q - y - x] := by
      funext d
      fin_cases d
      · rfl
      · rfl
      · change z = q - y - x
        omega
    have orbit : w ∈ faceWeightOrbit ![((faceMeshKeys q).get number).2,
        ((faceMeshKeys q).get number).1, q - ((faceMeshKeys q).get number).1 -
          ((faceMeshKeys q).get number).2] := by
      rw [at_key]
      refine Finset.mem_image.mpr ⟨σ.symm, Finset.mem_univ _, ?_⟩
      rw [← sorted]
      funext d
      simp
    let label : FacePerimeterIndex q := (t.1, ⟨number, ⟨w, orbit⟩⟩)
    refine ⟨.inl label, site_weights.symm, ?_⟩
    change Nonempty (MeshStarRealization (siteOfCorner t k)
      (face q ((faceMeshKeys q).get number).1 ((faceMeshKeys q).get number).2))
    rw [at_key]
    exact ⟨first_site ▸ model ▸ S.mapStar hq R⟩
  have xzero : x = 0 := by omega
  by_cases ypos : 0 < y
  · have zsmall : z < q := by omega
    let c := (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 0 2)
    let ρ := c.trans σ
    let t₀ : MeshFace q := (0, seamBaseCell zpos zsmall 0)
    obtain ⟨S, sf, sc⟩ := MacroMeshSymmetry.exists_ordered t.1 ρ
    have prior : w (ρ 0) = q - z := by
      change y = q - z
      omega
    have last : w (ρ 1) = z := rfl
    have other : w (ρ 2) = 0 := xzero
    have weights (d : Fin 3) :
        localGridWeights t₀.2 0 d = w (S.corner t₀.1 d) := by
      change localGridWeights (seamBaseCell zpos zsmall 0) 0 d = w (S.corner 0 d)
      rw [localGridWeights_seamBaseCell_zero, sc]
      fin_cases d
      · exact prior.symm
      · rfl
      · exact other.symm
    have site := S.meshSiteEquiv_siteOfCorner_eq_of_localGridWeights hq t₀ t 0 k sf weights
    obtain ⟨R⟩ := nonempty_referenceSeamStarRealization hq zpos zsmall
    have first_site : S.meshSiteEquiv hq (referenceSeamSite zpos zsmall) = siteOfCorner t k := site
    have key : z ∈ seamMeshKeys q := mem_seamMeshKeys.mpr ⟨by omega, zsmall⟩
    obtain ⟨number, at_key⟩ := List.mem_iff_get.mp key
    have matched : Nonempty (MeshStarRealization (siteOfCorner t k)
        (seam q ((seamMeshKeys q).get number))) := by
      rw [at_key]
      exact ⟨first_site ▸ S.mapStar hq R⟩
    let a := faceVertex t.1 (ρ 0)
    let b := faceVertex t.1 (ρ 1)
    have ab : a ≠ b := (faceVertex_injective t.1).ne (ρ.injective.ne (by decide))
    have adjacent : Adjacent a b := adjacent_faceVertex t.1 (ρ.injective.ne (by decide))
    have labels : extendFaceWeights t.1 w = edgeBarycentricWeights a b (q - z, z) :=
      extendFaceWeights_two t.1 ρ w prior last other
    by_cases order : a < b
    · have mem : (q - z, z) ∈ seamWeightOrbit q ((seamMeshKeys q).get number) := by
        rw [at_key]
        simp [seamWeightOrbit]
      let label : SeamPerimeterIndex q := (⟨(a, b), order, adjacent⟩, ⟨number, ⟨_, mem⟩⟩)
      exact ⟨.inr (.inl label), labels.symm.trans site_weights.symm, matched⟩
    · have mem : (z, q - z) ∈ seamWeightOrbit q ((seamMeshKeys q).get number) := by
        rw [at_key]
        simp [seamWeightOrbit]
      let label : SeamPerimeterIndex q :=
        (⟨(b, a), lt_of_le_of_ne (le_of_not_gt order) ab.symm, adjacent.reverse⟩,
          ⟨number, ⟨_, mem⟩⟩)
      exact ⟨.inr (.inl label), (edgeBarycentricWeights_swap ab _ _).symm.trans
        (labels.symm.trans site_weights.symm), matched⟩
  have yzero : y = 0 := by omega
  let ρ := (Equiv.swap (0 : Fin 3) 2).trans σ
  let t₀ := referenceVertexFineFace hq 0
  obtain ⟨S, sf, sc⟩ := MacroMeshSymmetry.exists_ordered t.1 ρ
  have one : w (ρ 0) = q := by
    change z = q
    omega
  have two : w (ρ 1) = 0 := yzero
  have three : w (ρ 2) = 0 := xzero
  have weights (d : Fin 3) :
      localGridWeights t₀.2 0 d = w (S.corner t₀.1 d) := by
    change localGridWeights (referenceVertexCell hq) 0 d = w (S.corner 0 d)
    rw [localGridWeights_referenceVertexCell, sc]
    fin_cases d
    · exact one.symm
    · exact two.symm
    · exact three.symm
  have site := S.meshSiteEquiv_siteOfCorner_eq_of_localGridWeights hq t₀ t 0 k sf weights
  obtain ⟨R⟩ := nonempty_referenceVertexStarRealization hq
  have first_site : S.meshSiteEquiv hq (referenceVertexSite hq) = siteOfCorner t k := site
  refine ⟨.inr (.inr (faceVertex t.1 (ρ 0))), ?_, ⟨first_site ▸ S.mapStar hq R⟩⟩
  rw [site_weights, extendFaceWeights_two t.1 ρ w one two three]
  funext v
  simp [perimeterIndexWeights, edgeBarycentricWeights]

end Unfoldings.FewestNets.Icosahedron
