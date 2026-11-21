module

public import Unfoldings.FewestNets.IcosahedronRealizedCorner
public import Unfoldings.FewestNets.IcosahedronRealizedInteriorStar
public import Unfoldings.FewestNets.FiniteMeshCornerExample

/-! The first finite corner certificate applies to the actual frequency-100 mesh. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductGeometry Real MeshStar

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- For the first interior orbit representative in each macroface, the six
actual Voronoi corners satisfy the altitude and incident-angle checks. -/
theorem actual_corner_bounds_q100_face_one_one (f : Fin 20)
    (o : Orientation ℝ Plane (Fin 2)) :
    let hq : 0 < (100 : ℕ) := by decide
    let a := interiorStarSite f (i := 1) (j := 98) (by decide) (by decide)
      (by decide : 1 + 98 < 100)
    ∀ t : MeshFace 100, (a : Space) ∈ Set.range (inscribedCorners t) →
      ∃ j k : Fin 3, j ≠ k ∧
        (a : Space) ∈ Set.range (inscribedCorners (adjacentFace hq t j)) ∧
        (a : Space) ∈ Set.range (inscribedCorners (adjacentFace hq t k)) ∧
        tan ((101 / 100 : ℝ) * (icosahedronEdge / 700)) < cornerGuardAltitude o hq t j k ∧
        107 * π / 180 < angle (minorArcTangent (facetNormal hq t)
          (facetNormal hq (adjacentFace hq t j))) (minorArcTangent (facetNormal hq t)
          (facetNormal hq (adjacentFace hq t k))) := by
  dsimp only
  let hq : 0 < (100 : ℕ) := by decide
  let M := modelInteriorStar 100 1 98
  have model : M = face 100 1 1 := modelInteriorStar_eq_face (by decide : 1 + 98 < 100)
  obtain ⟨R⟩ := nonempty_interiorStarRealization hq f (i := 1) (j := 98)
    (by decide) (by decide) (by decide)
  have outward (l : Fin 6) : 0 < inner ℝ M.direction (M.dual l) := by
    rw [model]
    exact (dualAngle_q100_face_one_one l).1
  intro t mem
  obtain ⟨l, rfl⟩ := R.complete t mem
  have flags : ∀ l : Fin 6, l ≠ l - 1 ∧ l ≠ l + 1 := by decide +kernel
  have bound := corner_bounds_q100_face_one_one l
  have altitude : tan ((101 / 100 : ℝ) * (icosahedronEdge / 700)) <
      meshCornerAltitude (M.cornerRay l (l - 1)) (M.cornerRay l (l + 1)) := model.symm ▸ bound.1
  have cosine : meshCornerCosine (M.cornerRay l (l - 1)) (M.cornerRay l (l + 1)) <
      cos (107 * π / 180) := model.symm ▸ bound.2
  have geometric := R.cornerAltitude_and_angle_of_model (by decide : 100 ≤ 100) hq o l
    (flags l).1 (flags l).2 outward (by positivity) (by linarith [pi_pos]) altitude cosine
  refine ⟨R.index l 2, R.index l 1, (R.index l).injective.ne (by decide), ?_, ?_, geometric⟩
  · rw [R.adjacentFace_pred (by decide : 100 ≤ 100) hq l (flags l).1]
    exact R.site_mem_face (l - 1)
  · rw [R.adjacentFace_succ (by decide : 100 ≤ 100) hq l (flags l).2]
    exact R.site_mem_face (l + 1)

end Unfoldings.FewestNets.Icosahedron
