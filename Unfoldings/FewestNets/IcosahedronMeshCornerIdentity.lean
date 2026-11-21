module

public import Unfoldings.FewestNets.IcosahedronWeightUniqueness
public import Unfoldings.FewestNets.IcosahedronGridBoxes

/-! A unit site determines its underlying global integer grid weights. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open NormedSpace
open scoped BigOperators

theorem chordCorners_eq_of_inscribedCorners_eq {q : ℕ} (hq : 0 < q)
    (t s : MeshFace q) (i j : Fin 3) (eq : inscribedCorners t i = inscribedCorners s j) :
    chordCorners t i = chordCorners s j := by
  have front (f : MeshFace q) (k : Fin 3) : chordCorners f k ∈ frontier hull :=
    faceTriangle_subset_frontier f.1 (chordTriangle_subset_faceTriangle hq f
      (subset_convexHull ℝ _ (Set.mem_range_self k)))
  have rpos (f : MeshFace q) (k : Fin 3) : 0 < ‖chordCorners f k‖ :=
    norm_pos_iff.mpr (chordCorners_ne_zero hq f k)
  apply frontier_eq_of_radial_rays_meet (show Convex ℝ hull from convex_convexHull ℝ _)
    zero_mem_interior_hull (front t i) (front s j) (rpos s j) (rpos t i)
  simp only [zero_add, sub_zero]
  have same := congrArg (fun v : Space => (‖chordCorners s j‖ * ‖chordCorners t i‖) • v) eq
  rw [mul_smul, mul_comm ‖chordCorners s j‖, mul_smul] at same
  simpa only [inscribedCorners, norm_smul_normalize] using same

theorem gridWeights_eq_of_chordCorners_eq {q : ℕ} (hq : 0 < q)
    (t s : MeshFace q) (i j : Fin 3) (eq : chordCorners t i = chordCorners s j) :
    gridWeights t i = gridWeights s j := by
  let u : Fin 12 → ℝ := fun k => (gridWeights t i k : ℝ) / q
  let v : Fin 12 → ℝ := fun k => (gridWeights s j k : ℝ) / q
  have left : chordCorners t i = ∑ k, u k • rawVertex k := chordCorners_eq_gridWeights hq t i
  have right : chordCorners s j = ∑ k, v k • rawVertex k := chordCorners_eq_gridWeights hq s j
  have member : chordCorners t i ∈ faceTriangle t.1 :=
    chordTriangle_subset_faceTriangle hq t (subset_convexHull ℝ _ (Set.mem_range_self i))
  have qne : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have total (f : MeshFace q) (l : Fin 3) :
      (∑ k, (gridWeights f l k : ℝ) / q) = 1 := by
    rw [← Finset.sum_div, ← Nat.cast_sum, sum_gridWeights, div_self qne]
  have weights := eq_face_weights t.1 u v (fun k => by dsimp [u]; positivity)
    (fun k => by dsimp [v]; positivity) (total t i) (total s j) (left ▸ member)
    (left.symm.trans (eq.trans right))
  funext k
  have h := (div_left_inj' qne).mp (congrFun weights k)
  exact_mod_cast h

theorem gridWeights_eq_of_inscribedCorners_eq {q : ℕ} (hq : 0 < q)
    (t s : MeshFace q) (i j : Fin 3) (eq : inscribedCorners t i = inscribedCorners s j) :
    gridWeights t i = gridWeights s j :=
  gridWeights_eq_of_chordCorners_eq hq t s i j
    (chordCorners_eq_of_inscribedCorners_eq hq t s i j eq)

end Unfoldings.FewestNets.Icosahedron
