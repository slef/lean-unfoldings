module

public import Unfoldings.FewestNets.IcosahedronGridAverages
public import Unfoldings.Geometry.IntegerCoordinateWeights

/-! Fine triangles meet exactly along the convex hulls of their common corners. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open scoped BigOperators

private theorem exists_commonGridWeights {q : ℕ} (t s : MeshFace q) (u v : Fin 3 → ℝ)
    (up : ∀ k, 0 ≤ u k) (vp : ∀ k, 0 ≤ v k) (us : ∑ k, u k = 1) (vs : ∑ k, v k = 1)
    (same : gridAverage t u = gridAverage s v) (k : Fin 3) (positive : 0 < u k) :
    ∃ l : Fin 3, gridWeights s l = gridWeights t k := by
  apply exists_gridWeights_of_bounds s _ (sum_gridWeights t k)
  intro i
  let value (j : Fin 3) : ℤ := gridWeights t j i
  have lo : (gridMin s i : ℝ) ≤ gridAverage t u i :=
    (congrFun same i).symm ▸ (gridAverage_bounds s v vp vs i).1
  have hi : gridAverage t u i ≤ (gridMax s i : ℝ) :=
    (congrFun same i).symm ▸ (gridAverage_bounds s v vp vs i).2
  have spread (a b : Fin 3) : value a ≤ value b + 1 := by
    have ha := (gridWeights_bounds t a i).2
    have hb := (gridWeights_bounds t b i).1
    have max := gridMax_le_gridMin_succ t i
    dsimp [value]
    omega
  have lo' : ((gridMin s i : ℤ) : ℝ) ≤ ∑ j, u j * (value j : ℝ) := by
    simpa only [value, Int.cast_natCast, gridAverage] using lo
  have hi' : (∑ j, u j * (value j : ℝ)) ≤ ((gridMax s i : ℤ) : ℝ) := by
    simpa only [value, Int.cast_natCast, gridAverage] using hi
  have lower := intCoordinate_ge_of_average_ge value u k (fun j => spread j k) up us positive lo'
  have upper := intCoordinate_le_of_average_le value u k (spread k) up us positive hi'
  change (gridMin s i : ℤ) ≤ (gridWeights t k i : ℤ) at lower
  change (gridWeights t k i : ℤ) ≤ (gridMax s i : ℤ) at upper
  exact ⟨by exact_mod_cast lower, by exact_mod_cast upper⟩

/-- The positive constituents of a convex combination in a neighboring
triangle are corners of both triangles. -/
theorem chordCorners_mem_of_positive_combination {q : ℕ} (hq : 0 < q) (t s : MeshFace q)
    (u : Fin 3 → ℝ) (up : ∀ k, 0 ≤ u k) (us : ∑ k, u k = 1)
    (member : (∑ k, u k • chordCorners t k) ∈ convexHull ℝ (Set.range (chordCorners s)))
    (k : Fin 3) (positive : 0 < u k) : chordCorners t k ∈ Set.range (chordCorners s) := by
  obtain ⟨v, vp, vs, xv⟩ := TriangleGrid.exists_weights_of_mem_convexHull_range _ member
  have same := gridAverage_eq_of_same_point hq t s u v up vp us vs xv.symm
  obtain ⟨l, e⟩ := exists_commonGridWeights t s u v up vp us vs same k positive
  refine ⟨l, ?_⟩
  rw [chordCorners_eq_gridWeights hq, chordCorners_eq_gridWeights hq, e]

/-- Any point of the intersection is a convex combination of exactly shared
corner positions, even when the two triangles belong to different macrofaces. -/
theorem chordTriangle_inter {q : ℕ} (hq : 0 < q) (t s : MeshFace q) :
    convexHull ℝ (Set.range (chordCorners t)) ∩ convexHull ℝ (Set.range (chordCorners s)) =
      convexHull ℝ (Set.range (chordCorners t) ∩ Set.range (chordCorners s)) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨ht, hs⟩
    obtain ⟨u, up, us, xu⟩ := TriangleGrid.exists_weights_of_mem_convexHull_range _ ht
    have shared (k : Fin 3) (hk : 0 < u k) : chordCorners t k ∈ Set.range (chordCorners s) :=
      chordCorners_mem_of_positive_combination hq t s u up us (xu.symm ▸ hs) k hk
    let positive := Finset.univ.filter (fun k : Fin 3 => 0 < u k)
    have zero (k : Fin 3) (_ : k ∈ Finset.univ) (absent : k ∉ positive) : u k = 0 := by
      have nonpos := not_lt.mp (fun h => absent (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      exact le_antisymm nonpos (up k)
    have total : ∑ k ∈ positive, u k = 1 := by
      rw [Finset.sum_subset (Finset.subset_univ _) zero, us]
    have point : ∑ k ∈ positive, u k • chordCorners t k = x := by
      rw [Finset.sum_subset (Finset.subset_univ _) (fun k hk h => by
        rw [zero k hk h, zero_smul]), xu]
    rw [← point, ← Finset.centerMass_eq_of_sum_1 _ _ total]
    apply Finset.centerMass_mem_convexHull _ (fun k _ => up k) (total.symm ▸ zero_lt_one)
    intro k hk
    exact ⟨Set.mem_range_self k, shared k (Finset.mem_filter.mp hk).2⟩
  · exact Set.subset_inter
      (convexHull_mono Set.inter_subset_left) (convexHull_mono Set.inter_subset_right)

end Unfoldings.FewestNets.Icosahedron
