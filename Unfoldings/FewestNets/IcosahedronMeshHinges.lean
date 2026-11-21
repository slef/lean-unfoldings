module

public import Unfoldings.FewestNets.IcosahedronMeshGauge
public import Unfoldings.FewestNets.IcosahedronAcuteGrid
public import Unfoldings.Geometry.RadialCommonEdge
public import Unfoldings.Geometry.RadialTriangleReindex

/-! The actual fine triangles support their neighbors across every common radial edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductGeometry
open scoped BigOperators

private theorem meshGauge_lt_of_common_edge {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t s : MeshFace q) {i j k i' j' k' : Fin 3}
    (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k) (ij' : i' ≠ j') (ik' : i' ≠ k') (jk' : j' ≠ k')
    (hi : inscribedCorners s i' = inscribedCorners t i)
    (hj : inscribedCorners s j' = inscribedCorners t j)
    (absent : inscribedCorners t k ∉ Set.range (inscribedCorners s)) :
    meshGauge hq t (inscribedCorners s k') < 1 := by
  let a := inscribedCorners t i
  let b := inscribedCorners t j
  let c := inscribedCorners t k
  let d := inscribedCorners s k'
  obtain ⟨left, lrange⟩ := permuted_triangle_corners (linearIndependent_inscribedCorners hq t)
    ij ik jk
  have right_data := permuted_triangle_corners (linearIndependent_inscribedCorners hq s)
    ij' ik' jk'
  rw [hi, hj] at right_data
  obtain ⟨right, rrange⟩ := right_data
  change LinearIndependent ℝ ![a, b, c] at left
  change LinearIndependent ℝ ![a, b, d] at right
  have leq := radialTriangleCone_eq_of_range_eq left
    (linearIndependent_inscribedCorners hq t) lrange
  have req := radialTriangleCone_eq_of_range_eq right
    (linearIndependent_inscribedCorners hq s) rrange
  have gauge := radialTriangleGauge_eq_of_range_eq left
    (linearIndependent_inscribedCorners hq t) lrange
  let L := (radialTriangleBasis left).coord 2
  have at_a : L a = 0 := by
    change (radialTriangleBasis left).coord 2 (![a, b, c] (0 : Fin 3)) = 0
    rw [radialTriangleBasis_coord_corner]
    norm_num
  have at_b : L b = 0 := by
    change (radialTriangleBasis left).coord 2 (![a, b, c] (1 : Fin 3)) = 0
    rw [radialTriangleBasis_coord_corner]
    norm_num
  have on_edge (x : Space) (ht : x ∈ radialTriangleCone ![a, b, c])
      (hs : x ∈ radialTriangleCone ![a, b, d]) : L x = 0 := by
    by_cases zero : x = 0
    · rw [zero, map_zero]
    obtain ⟨w, nonnegative, xeq, share⟩ := exists_shared_corner_expansion hq t s zero
      (leq ▸ ht) (req ▸ hs)
    have wk : w k = 0 := le_antisymm (le_of_not_gt fun pos => absent (share k pos)) (nonnegative k)
    rw [xeq, map_sum]
    apply Finset.sum_eq_zero
    intro l _
    obtain ⟨m, hm⟩ := (vector_three_bijective ij ik jk).2 l
    fin_cases m
    · change i = l at hm
      rw [← hm, map_smul]
      change w i • L a = 0
      rw [at_a, smul_zero]
    · change j = l at hm
      rw [← hm, map_smul]
      change w j • L b = 0
      rw [at_b, smul_zero]
    · change k = l at hm
      rw [← hm, wk, zero_smul, map_zero]
  have acute_c : angle (a - c) (b - c) < Real.pi / 2 :=
    angle_inscribedCorners_lt_pi_div_two qbig t k i j ik.symm jk.symm ij
  have acute_d : angle (a - d) (b - d) < Real.pi / 2 := by
    dsimp only [a, b, d]
    rw [← hi, ← hj]
    exact angle_inscribedCorners_lt_pi_div_two qbig s k' i' j' ik'.symm jk'.symm ij'
  have lower := radialTriangleGauge_lt_of_acute_common_edge left right on_edge
    (inscribedCorners_unit hq t i) (inscribedCorners_unit hq t j)
    (inscribedCorners_unit hq t k) (inscribedCorners_unit hq s k') acute_c acute_d
  rw [gauge] at lower
  exact lower

private theorem meshGauge_on_neighbor_corner {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t s : MeshFace q) {x : Space} (off : ∀ k : Fin 3, ∀ r : ℝ, x ≠ r • inscribedCorners t k)
    (ht : x ∈ radialTriangleCone (inscribedCorners t))
    (hs : x ∈ radialTriangleCone (inscribedCorners s)) (l : Fin 3) :
    meshGauge hq t (inscribedCorners s l) ≤ 1 ∧
      (inscribedCorners s l ∉ Set.range (inscribedCorners t) →
        meshGauge hq t (inscribedCorners s l) < 1) := by
  by_cases full : Set.range (inscribedCorners t) ⊆ Set.range (inscribedCorners s)
  · choose pick hpick using (fun i => full (Set.mem_range_self i))
    have injective : Function.Injective pick := by
      intro a b eq
      exact (linearIndependent_inscribedCorners hq t).injective
        ((hpick a).symm.trans ((congrArg (inscribedCorners s) eq).trans (hpick b)))
    obtain ⟨k, hk⟩ := (Finite.injective_iff_bijective.mp injective).2 l
    have eq : inscribedCorners s l = inscribedCorners t k := hk ▸ hpick k
    rw [eq, meshGauge_corner]
    exact ⟨le_rfl, fun absent => (absent (Set.mem_range_self k)).elim⟩
  obtain ⟨_, ⟨k, rfl⟩, absent⟩ := Set.not_subset.mp full
  obtain ⟨i, j, ij, common_i, common_j⟩ := exists_two_shared_corners hq t s off ht hs
  have ik : i ≠ k := fun eq => absent (eq ▸ common_i)
  have jk : j ≠ k := fun eq => absent (eq ▸ common_j)
  obtain ⟨i', hi⟩ := common_i
  obtain ⟨j', hj⟩ := common_j
  have ij' : i' ≠ j' := by
    intro eq
    exact ij ((linearIndependent_inscribedCorners hq t).injective
      (hi.symm.trans ((congrArg (inscribedCorners s) eq).trans hj)))
  obtain ⟨k', ik', jk', every⟩ := exists_fin_three_rest i' j' ij'
  rcases every l with rfl | rfl | rfl
  · rw [hi, meshGauge_corner]
    exact ⟨le_rfl, fun absent => (absent (Set.mem_range_self i)).elim⟩
  · rw [hj, meshGauge_corner]
    exact ⟨le_rfl, fun absent => (absent (Set.mem_range_self j)).elim⟩
  · have strict := meshGauge_lt_of_common_edge qbig hq t s ij ik jk ij' ik' jk' hi hj absent
    exact ⟨strict.le, fun _ => strict⟩

/-- Away from corner rays, every adjoining cell lies on the supporting side
of the other cell's chord plane. -/
theorem meshGauge_le_on_neighbor {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t s : MeshFace q) {x : Space} (off : ∀ k : Fin 3, ∀ r : ℝ, x ≠ r • inscribedCorners t k)
    (ht : x ∈ radialTriangleCone (inscribedCorners t))
    (hs : x ∈ radialTriangleCone (inscribedCorners s))
    {z : Space} (hz : z ∈ radialTriangleCone (inscribedCorners s)) :
    meshGauge hq t z ≤ meshGauge hq s z :=
  linear_le_gauge_on_radialTriangleCone _ (meshGauge hq t)
    (fun l => (meshGauge_on_neighbor_corner qbig hq t s off ht hs l).1) hz

theorem meshGauge_lt_on_neighbor_of_outside {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t s : MeshFace q) {x : Space} (off : ∀ k : Fin 3, ∀ r : ℝ, x ≠ r • inscribedCorners t k)
    (ht : x ∈ radialTriangleCone (inscribedCorners t))
    (hs : x ∈ radialTriangleCone (inscribedCorners s))
    {z : Space} (hz : z ∈ radialTriangleCone (inscribedCorners s))
    (outside : z ∉ radialTriangleCone (inscribedCorners t)) :
    meshGauge hq t z < meshGauge hq s z := by
  obtain ⟨w, nonnegative, eq⟩ := hz
  have exists_outside : ∃ l, 0 < w l ∧ inscribedCorners s l ∉ Set.range (inscribedCorners t) := by
    by_contra! all
    apply outside
    rw [eq]
    exact sum_mem_radialTriangleCone (linearIndependent_inscribedCorners hq t) w nonnegative all
  rw [eq, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul, meshGauge_corner]
  refine Finset.sum_lt_sum ?_ ?_
  · intro l _
    exact mul_le_mul_of_nonneg_left (meshGauge_on_neighbor_corner qbig hq t s off ht hs l).1
      (nonnegative l)
  · obtain ⟨l, pos, missing⟩ := exists_outside
    exact ⟨l, Finset.mem_univ _, mul_lt_mul_of_pos_left
      ((meshGauge_on_neighbor_corner qbig hq t s off ht hs l).2 missing) pos⟩

end Unfoldings.FewestNets.Icosahedron
