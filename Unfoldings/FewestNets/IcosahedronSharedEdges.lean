module

public import Unfoldings.FewestNets.IcosahedronFacetNormals

/-! Each fine edge has an incident triangle on the other radial side. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open Set Filter
open scoped BigOperators Topology

/-- Two distinct corners of one fine triangle appear in a distinct triangle
across their edge, with a corner absent from the first triangle. -/
theorem exists_meshNeighbor_of_edge {q : ℕ} (hq : 0 < q) (t : MeshFace q)
    (i j : Fin 3) (ij : i ≠ j) :
    ∃ s : MeshFace q, inscribedCorners t i ∈ Set.range (inscribedCorners s) ∧
      inscribedCorners t j ∈ Set.range (inscribedCorners s) ∧
      ∃ d : Fin 3, inscribedCorners s d ∉ Set.range (inscribedCorners t) := by
  obtain ⟨k, ik, jk, _⟩ := exists_fin_three_rest i j ij
  let independent := linearIndependent_inscribedCorners hq t
  let B := radialTriangleBasis independent
  let x := inscribedCorners t i + inscribedCorners t j
  have x_coord (l : Fin 3) :
      B.coord l x = (if l = i then 1 else 0) + (if l = j then 1 else 0) := by
    dsimp only [x, B]
    rw [map_add, radialTriangleBasis_coord_corner, radialTriangleBasis_coord_corner]
  have in_t : x ∈ radialTriangleCone (inscribedCorners t) := by
    apply (mem_radialTriangleCone_iff_basis independent).mpr
    intro l
    change 0 ≤ B.coord l x
    rw [x_coord]
    positivity
  have x_ne : x ≠ 0 := by
    intro zero
    have hx := x_coord i
    rw [zero, map_zero] at hx
    simp [ij] at hx
  let path (r : ℝ) := x - r • inscribedCorners t k
  have near : Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    have c : Continuous path := by dsimp [path]; fun_prop
    simpa only [ContinuousWithinAt, path, zero_smul, sub_zero] using
      (c.continuousWithinAt (s := Ioi (0 : ℝ)) (x := (0 : ℝ)))
  have close := near.eventually (eventually_meshCones_contain_base hq x)
  have positive : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, rpos⟩ := (close.and positive).exists
  obtain ⟨s, in_s⟩ := radialMesh_cover hq (path r)
  have contact := hr s in_s
  have outside : path r ∉ radialTriangleCone (inscribedCorners t) := by
    intro member
    have h := (mem_radialTriangleCone_iff_basis independent).mp member k
    change 0 ≤ B.coord k (path r) at h
    dsimp only [path] at h
    rw [map_sub, map_smul, x_coord] at h
    change 0 ≤ _ - r • (radialTriangleBasis independent).coord k (inscribedCorners t k) at h
    rw [radialTriangleBasis_coord_corner] at h
    simp [ik.symm, jk.symm, smul_eq_mul] at h
    exact rpos.not_ge h
  obtain ⟨w, _, eq, shared⟩ := exists_shared_corner_expansion hq t s x_ne in_t contact
  have weight (l : Fin 3) : B.coord l x = w l := by
    rw [eq]
    exact radialTriangleBasis_coord_eq_weight independent w l
  have i_pos : 0 < w i := by rw [← weight, x_coord]; simp [ij]
  have j_pos : 0 < w j := by rw [← weight, x_coord]; simp [ij.symm]
  refine ⟨s, shared i i_pos, shared j j_pos, ?_⟩
  by_contra! full
  exact outside (radialTriangleCone_mono_range independent (by
    rintro _ ⟨k, rfl⟩
    exact full k) in_s)

end Unfoldings.FewestNets.Icosahedron
