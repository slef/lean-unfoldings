module

public import Unfoldings.FewestNets.IcosahedronLabeledStars
public import Unfoldings.FewestNets.IcosahedronRealizedPerimeter
public import Unfoldings.FewestNets.FiniteMeshPerimeterBounds
public import Unfoldings.FewestNets.FiniteMeshCorner100Bounds

/-! Transfer the finite model perimeter bounds to the actual network. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductGeometry
open scoped BigOperators

/-- The global barycentric labels bound the actual network length by the
orbit-weighted sum of the certified model perimeters. -/
theorem networkLength_le_weightedArcUpperTotal {q : ℕ} [Fintype (MeshEdge q)]
    (qbig : 100 ≤ q) (hq : 0 < q)
    (interior : ∀ i j, (i, j) ∈ faceMeshKeys q → ∀ k,
      0 < inner ℝ (MeshStar.face q i j).direction ((MeshStar.face q i j).dual k))
    (seam : ∀ i, i ∈ seamMeshKeys q → ∀ k,
      0 < inner ℝ (MeshStar.seam q i).direction ((MeshStar.seam q i).dual k))
    (pentagon : ∀ k, 0 < inner ℝ (MeshStar.pentagon q).direction ((MeshStar.pentagon q).dual k)) :
    networkLength (meshEndpoint hq) ≤ weightedArcUpperTotal q := by
  classical
  let : Fintype (meshSites q) := Fintype.ofFinite _
  choose label weights realization using (exists_perimeterIndex_realizing hq)
  have injective : Function.Injective label := fun a b same =>
    (meshSiteWeights_injective hq)
      ((weights a).symm.trans ((congrArg perimeterIndexWeights same).trans (weights b)))
  have flags6 : ∀ k : Fin 6, k ≠ k + 1 ∧ k ≠ k - 1 ∧ k + 2 ≠ k := by decide +kernel
  have flags5 : ∀ k : Fin 5, k ≠ k + 1 ∧ k ≠ k - 1 ∧ k + 2 ≠ k := by decide +kernel
  have perim_le (a : meshSites q) : meshSitePerimeter hq a ≤ perimeterIndexUpper (label a) := by
    generalize hl : label a = l
    have r : perimeterIndexRealizes a l := hl ▸ realization a
    rcases l with f | e | v
    · let key := (faceMeshKeys q).get f.2.1
      obtain ⟨R⟩ : Nonempty (MeshStarRealization a (MeshStar.face q key.1 key.2)) := r
      exact R.meshSitePerimeter_le_arcUpper qbig hq flags6 (interior _ _ (List.get_mem _ _))
    · let key := (seamMeshKeys q).get e.2.1
      obtain ⟨R⟩ : Nonempty (MeshStarRealization a (MeshStar.seam q key)) := r
      exact R.meshSitePerimeter_le_arcUpper qbig hq flags6 (seam _ (List.get_mem _ _))
    · obtain ⟨R⟩ : Nonempty (MeshStarRealization a (MeshStar.pentagon q)) := r
      exact R.meshSitePerimeter_le_arcUpper qbig hq flags5 pentagon
  have bound : (∑ a : meshSites q, meshSitePerimeter hq a) ≤
      ∑ l : PerimeterIndex q, perimeterIndexUpper l := calc
    _ ≤ ∑ a : meshSites q, perimeterIndexUpper (label a) :=
      Finset.sum_le_sum fun a _ => perim_le a
    _ = ∑ l ∈ Finset.univ.image label, perimeterIndexUpper l := by
      rw [Finset.sum_image (fun _ _ _ _ same => injective same)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun l _ _ =>
      perimeterIndexUpper_nonneg l
  rw [networkLength_eq_half_sum_meshSitePerimeter,
    ← mul_le_mul_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
  rw [div_mul_cancel₀ _ (by norm_num), mul_comm, ← sum_perimeterIndexUpper]
  exact bound

/-- The actual frequency-100 dual arc length satisfies the paper's perimeter bound. -/
theorem networkLength_q100_lt [Fintype (MeshEdge 100)] :
    networkLength (meshEndpoint (by decide : 0 < (100 : ℕ))) < 2084 := by
  apply lt_of_le_of_lt (networkLength_le_weightedArcUpperTotal (by decide : 100 ≤ 100)
    (by decide) (fun _ _ key k => (q100_face_corner_bounds key k).1)
    (fun _ key k => (q100_seam_corner_bounds key k).1)
    (fun k => (q100_pentagon_corner_bounds k).1))
  exact weightedArcUpperTotal_q100

end Unfoldings.FewestNets.Icosahedron
