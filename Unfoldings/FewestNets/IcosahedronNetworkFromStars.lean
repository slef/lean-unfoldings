module

public import Unfoldings.FewestNets.IcosahedronRealizedCorner
public import Unfoldings.FewestNets.IcosahedronNetworkOfCornerBounds
public import Unfoldings.FewestNets.IcosahedronStarClassification

/-! The model star certificates exhaust the actual network's corner checks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real InnerProductGeometry

namespace MeshStar

/-- Local inequalities used for the angular separation and incident angles. -/
def CornerBounds {n : ℕ} (star : MeshStar (n + 1)) (r ψ : ℝ) : Prop :=
  ∀ k, 0 < inner ℝ star.direction (star.dual k) ∧
    tan r < meshCornerAltitude (star.cornerRay k (k - 1)) (star.cornerRay k (k + 1)) ∧
    meshCornerCosine (star.cornerRay k (k - 1)) (star.cornerRay k (k + 1)) < cos ψ

end MeshStar

namespace Icosahedron

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem MeshStarRealization.corner_bounds_at_site {q n : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (o : Orientation ℝ Plane (Fin 2)) {a : meshSites q} {M : MeshStar (n + 1)}
    (R : MeshStarRealization a M) (flags : ∀ l : Fin (n + 1), l ≠ l - 1 ∧ l ≠ l + 1)
    {r ψ : ℝ} (lo : 0 ≤ ψ) (hi : ψ ≤ π) (model : M.CornerBounds r ψ)
    (t : MeshFace q) {i j k : Fin 3} (at_i : siteOfCorner t i = a)
    (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k) :
    tan r ≤ cornerGuardAltitude o hq t j k ∧ ψ ≤ meshCornerAngle hq t j k := by
  have mem : (a : Space) ∈ Set.range (inscribedCorners t) :=
    ⟨i, congrArg Subtype.val at_i⟩
  obtain ⟨l, rfl⟩ := R.complete t mem
  have center : i = R.index l 0 := (siteOfCorner_injective hq (R.face l))
    (at_i.trans (Subtype.ext ((R.corner_eq l 0).trans R.center)).symm)
  obtain ⟨j', rfl⟩ := (R.index l).surjective j
  obtain ⟨k', rfl⟩ := (R.index l).surjective k
  have j0 : j' ≠ 0 := fun h => ij (center.trans (congrArg (R.index l) h.symm))
  have k0 : k' ≠ 0 := fun h => ik (center.trans (congrArg (R.index l) h.symm))
  have different : j' ≠ k' := fun h => jk (congrArg (R.index l) h)
  have bounds :
      tan r ≤ cornerGuardAltitude o hq (R.face l) (R.index l 2) (R.index l 1) ∧
        ψ ≤ meshCornerAngle hq (R.face l) (R.index l 2) (R.index l 1) := by
    have b := R.cornerAltitude_and_angle_of_model qbig hq o l (flags l).1 (flags l).2
      (fun x => (model x).1) lo hi (model l).2.1 (model l).2.2
    exact ⟨b.1.le, b.2.le⟩
  have choices : (j' = 1 ∧ k' = 2) ∨ (j' = 2 ∧ k' = 1) := by
    simpa only [zero_add] using fin_three_pair_complement j' k' 0 different j0 k0
  rcases choices with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [cornerGuardAltitude_comm, meshCornerAngle_comm]
    exact bounds
  · exact bounds

theorem meshCornerBounds_of_canonical_stars {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (o : Orientation ℝ Plane (Fin 2)) {r ψ : ℝ} (lo : 0 ≤ ψ) (hi : ψ ≤ π)
    (interior : ∀ i j, (i, j) ∈ faceMeshKeys q → (MeshStar.face q i j).CornerBounds r ψ)
    (seam : ∀ i, i ∈ seamMeshKeys q → (MeshStar.seam q i).CornerBounds r ψ)
    (pentagon : (MeshStar.pentagon q).CornerBounds r ψ)
    (t : MeshFace q) (j k : Fin 3) (jk : j ≠ k) :
    tan r ≤ cornerGuardAltitude o hq t j k ∧ ψ ≤ meshCornerAngle hq t j k := by
  obtain ⟨i, ji, ki, _⟩ := exists_fin_three_rest j k jk
  let a := siteOfCorner t i
  have flags6 : ∀ l : Fin 6, l ≠ l - 1 ∧ l ≠ l + 1 := by decide +kernel
  have flags5 : ∀ l : Fin 5, l ≠ l - 1 ∧ l ≠ l + 1 := by decide +kernel
  rcases meshSite_has_realizedModel hq a with ⟨x, y, key, ⟨R⟩⟩ | ⟨x, key, ⟨R⟩⟩ | ⟨R⟩
  · exact R.corner_bounds_at_site qbig hq o flags6 lo hi (interior x y key) t rfl ji.symm ki.symm jk
  · exact R.corner_bounds_at_site qbig hq o flags6 lo hi (seam x key) t rfl ji.symm ki.symm jk
  · obtain ⟨actual⟩ := R
    exact actual.corner_bounds_at_site qbig hq o flags5 lo hi pentagon t rfl ji.symm ki.symm jk

end Icosahedron
end Unfoldings.FewestNets
