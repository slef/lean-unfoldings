module

public import Unfoldings.Examples.Tetrahedron.Coordinates

/-! The tetrahedron's convex hull and its four actual triangular facets. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Examples.Tetrahedron

def coordinate (i : Fin 3) : Space →ₗ[ℝ] ℝ where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordinate_apply (i : Fin 3) (x : Space) : coordinate i x = x i := rfl

def weight : Fin 4 → Space →ᵃ[ℝ] ℝ :=
  ![AffineMap.const ℝ Space 1 - (coordinate 0).toAffineMap,
    (coordinate 0).toAffineMap - (coordinate 1).toAffineMap,
    (coordinate 1).toAffineMap - (coordinate 2).toAffineMap,
    (coordinate 2).toAffineMap]

theorem weight_vertex (i j : Fin 4) : weight i (vertex j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [weight, vertex, vec3]

theorem continuous_weight (i : Fin 4) : Continuous (weight i) := by
  fin_cases i <;> dsimp [weight] <;> fun_prop

theorem sum_weight (x : Space) : ∑ i, weight i x = 1 := by
  simp [weight, Fin.sum_univ_succ]

theorem sum_weight_vertex (x : Space) : ∑ i, weight i x • vertex i = x := by
  ext j
  fin_cases j <;> simp [weight, vertex, vec3, Fin.sum_univ_succ]

def hull : Set Space := convexHull ℝ (Set.range vertex)

theorem hull_eq_nonneg : hull = {x | ∀ i, 0 ≤ weight i x} := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro _ ⟨j, rfl⟩ i
      rw [weight_vertex]
      split_ifs <;> norm_num
    · simpa only [Set.preimage, Set.mem_Ici, Set.mem_singleton_iff,
        Set.ofPred_forall, Set.ofPred_and] using
        convex_iInter (fun i => (convex_Ici (0 : ℝ)).affine_preimage (weight i))
  · intro x nonnegative
    have member := affineCombination_mem_convexHull (v := vertex)
      (s := Finset.univ) (fun i _ => nonnegative i) (sum_weight x)
    rw [Finset.univ.affineCombination_eq_linear_combination _ _ (sum_weight x),
      sum_weight_vertex] at member
    exact member

def facet (f : Fin 4) : Set Space := convexHull ℝ (Set.range (vertex ∘ corner f))

theorem corner_ne (f : Fin 4) (i : Fin 3) : corner f i ≠ f := by
  fin_cases f <;> fin_cases i <;> decide

theorem facet_eq (f : Fin 4) : facet f = {x | (∀ i, 0 ≤ weight i x) ∧ weight f x = 0} := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro _ ⟨j, rfl⟩
      refine ⟨fun i => ?_, ?_⟩
      · rw [Function.comp_apply, weight_vertex]
        split_ifs <;> norm_num
      · rw [Function.comp_apply, weight_vertex, ite_eq_right (corner_ne f j).symm]
    · simpa only [Set.preimage, Set.mem_Ici, Set.mem_singleton_iff,
        Set.ofPred_forall, Set.ofPred_and] using
        (convex_iInter (fun i => (convex_Ici (0 : ℝ)).affine_preimage (weight i))).inter
          ((convex_singleton (0 : ℝ)).affine_preimage (weight f))
  · rintro x ⟨nonnegative, missing⟩
    have sum : ∑ i, weight (corner f i) x = 1 := by
      fin_cases f <;> simp [weight, corner, Fin.sum_univ_succ] at missing ⊢ <;> linarith
    have expression : ∑ i, weight (corner f i) x • vertex (corner f i) = x := by
      fin_cases f <;> ext j <;> fin_cases j <;>
        simp [weight, corner, vertex, vec3, Fin.sum_univ_succ] at missing ⊢ <;> linarith
    have member := affineCombination_mem_convexHull (v := vertex ∘ corner f)
      (s := Finset.univ) (fun i _ => nonnegative (corner f i)) sum
    rw [Finset.univ.affineCombination_eq_linear_combination _ _ sum] at member
    exact expression ▸ member

theorem closed_hull : IsClosed hull := (Set.finite_range vertex).isCompact_convexHull ℝ |>.isClosed

theorem strict_weights_mem_interior {x : Space} (positive : ∀ i, 0 < weight i x) :
    x ∈ interior hull := by
  let U : Set Space := {y | ∀ i, 0 < weight i y}
  have open_U : IsOpen U := by
    change IsOpen {y | ∀ i, 0 < weight i y}
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun i =>
      isOpen_lt (continuous_const (y := (0 : ℝ))) (continuous_weight i))
  have subset : U ⊆ hull := by
    rw [hull_eq_nonneg]
    exact fun _ member i => (member i).le
  exact interior_mono subset (open_U.interior_eq.symm ▸ positive)

theorem hull_interior_nonempty : (interior hull).Nonempty := by
  refine ⟨vec3 (3 / 4) (1 / 2) (1 / 4), strict_weights_mem_interior ?_⟩
  intro i
  fin_cases i <;> norm_num [weight, vec3]

theorem weight_surjective (f : Fin 4) : Function.Surjective (weight f) := by
  intro t
  refine ⟨AffineMap.lineMap (vertex (corner f 0)) (vertex f) t, ?_⟩
  rw [(weight f).apply_lineMap, weight_vertex, weight_vertex,
    ite_eq_right (corner_ne f 0).symm, ite_eq_left rfl]
  simp [AffineMap.lineMap_apply_ring]

theorem isOpen_weight (f : Fin 4) : IsOpenMap (weight f) := by
  let linear := (weight f).linear.toContinuousLinearMap
  have surjective : Function.Surjective linear :=
    (weight f).linear_surjective_iff.mpr (weight_surjective f)
  exact AffineMap.isOpenMap_linear_iff.mp (linear.isOpenMap surjective)

theorem zero_weight_not_mem_interior (f : Fin 4) {x : Space} (zero : weight f x = 0) :
    x ∉ interior hull := by
  have inclusion : hull ⊆ weight f ⁻¹' Set.Ici 0 := by
    rw [hull_eq_nonneg]
    exact fun _ hx => hx f
  intro inside
  have bound := (isOpen_weight f).interior_preimage_subset_preimage_interior
    (interior_mono inclusion inside)
  change weight f x ∈ interior (Set.Ici (0 : ℝ)) at bound
  rw [interior_Ici] at bound
  exact (lt_irrefl (0 : ℝ)) (zero ▸ bound)

theorem frontier_hull : frontier hull = ⋃ f, facet f := by
  ext x
  rw [closed_hull.frontier_eq, Set.mem_sdiff, Set.mem_iUnion]
  constructor
  · rintro ⟨inside, boundary⟩
    have nonnegative := hull_eq_nonneg ▸ inside
    have zero : ∃ f, weight f x = 0 := by
      by_contra none
      apply boundary
      apply strict_weights_mem_interior
      intro f
      exact lt_of_le_of_ne (nonnegative f) (fun equal => none ⟨f, equal.symm⟩)
    obtain ⟨f, zero⟩ := zero
    exact ⟨f, (facet_eq f).symm ▸ ⟨nonnegative, zero⟩⟩
  · rintro ⟨f, member⟩
    rw [facet_eq f] at member
    exact ⟨hull_eq_nonneg.symm ▸ member.1, zero_weight_not_mem_interior f member.2⟩

end Unfoldings.Examples.Tetrahedron
