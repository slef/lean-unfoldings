module

public import Unfoldings.FewestNets.IcosahedronIncidence
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-! The twenty coordinate triangles are the faces of the regular icosahedral hull. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open Real Set InnerProductSpace

def hull : Set Space := convexHull ℝ (Set.range rawVertex)

def faceCorners (f : Fin 20) (i : Fin 3) : Space := rawVertex (faceVertex f i)

def faceTriangle (f : Fin 20) : Set Space := convexHull ℝ (Set.range (faceCorners f))

private def axisEndpoints : Fin 3 → Fin 12 × Fin 12 := ![(10, 8), (3, 1), (7, 5)]

private theorem axisDifference (k : Fin 3) :
    rawVertex (axisEndpoints k).1 - rawVertex (axisEndpoints k).2 =
      (2 : ℝ) • EuclideanSpace.basisFun (Fin 3) ℝ k := by
  rw [EuclideanSpace.basisFun_apply]
  ext j
  fin_cases k <;> fin_cases j <;>
    norm_num [axisEndpoints, rawVertex, rawCoordinates, goldenValue, PiLp.single_apply]

theorem hull_interior_nonempty : (interior hull).Nonempty := by
  apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
  let A := affineSpan ℝ (Set.range rawVertex)
  have mem (i : Fin 12) : rawVertex i ∈ A := mem_affineSpan ℝ (Set.mem_range_self i)
  apply (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨_, mem 0⟩).mp
  let B := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  apply top_unique
  rw [← B.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  have hk := A.vsub_mem_direction (mem (axisEndpoints k).1) (mem (axisEndpoints k).2)
  change rawVertex (axisEndpoints k).1 - rawVertex (axisEndpoints k).2 ∈ A.direction at hk
  rw [axisDifference] at hk
  have h := A.direction.smul_mem (1 / 2 : ℝ) hk
  change EuclideanSpace.basisFun (Fin 3) ℝ k ∈ A.direction
  simpa [smul_smul] using h

theorem exists_inner_rawVertex_pos {n : Space} (hn : n ≠ 0) :
    ∃ i : Fin 12, 0 < inner ℝ n (rawVertex i) := by
  by_contra! h
  have zero (i : Fin 12) : inner ℝ n (rawVertex i) = 0 := by
    have hi := h (antipode i)
    rw [rawVertex_antipode, inner_neg_right] at hi
    exact le_antisymm (h i) (neg_nonpos.mp hi)
  apply hn
  ext k
  have hk := congrArg (inner ℝ n) (axisDifference k)
  rw [inner_sub_right, zero, zero, sub_self, real_inner_smul_right,
    EuclideanSpace.inner_basisFun_real] at hk
  change n k = 0
  linarith only [hk]

theorem zero_mem_interior_hull : (0 : Space) ∈ interior hull := by
  by_contra h
  obtain ⟨f, hf, support⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (convex_convexHull ℝ _) h hull_interior_nonempty
  let n := (toDual ℝ Space).symm f
  have hn : n ≠ 0 := by
    intro eq
    exact hf ((toDual ℝ Space).symm.injective (eq.trans (map_zero _).symm))
  obtain ⟨i, hi⟩ := exists_inner_rawVertex_pos hn
  rw [toDual_symm_apply] at hi
  have le := support _ (subset_convexHull ℝ _ (Set.mem_range_self i))
  rw [map_zero] at le
  exact hi.not_ge le

theorem adjacent_of_maximizers {n : Space} {m : ℝ} (hm : 0 < m)
    (bound : ∀ i : Fin 12, inner ℝ n (rawVertex i) ≤ m) {i j : Fin 12} (ij : i ≠ j)
    (hi : inner ℝ n (rawVertex i) = m) (hj : inner ℝ n (rawVertex j) = m) :
    Adjacent i j := by
  by_contra h
  have data := dotData_classify i j
  rw [ite_eq_right_iff.mpr (fun eq => (ij eq).elim),
    ite_eq_right_iff.mpr (fun eq => (h eq).elim)] at data
  by_cases low : dotData i j = (0, -1)
  · obtain ⟨a, b, hab⟩ := exists_pair_beyond i j low
    have eq := congrArg (inner ℝ n) hab
    rw [inner_add_right, real_inner_smul_right, inner_add_right, hi, hj] at eq
    have strict := mul_lt_mul_of_pos_right one_lt_goldenRatio (add_pos hm hm)
    linarith only [eq, strict, bound a, bound b]
  · rw [ite_eq_right low] at data
    rw [dotData_antipode_of_eq i j data, rawVertex_antipode, inner_neg_right, hi] at hj
    linarith only [hj, hm]

/-- Any mutually adjacent set of corners lies in one macroface. -/
theorem exists_face_covering_clique {S : Set (Fin 12)}
    (adj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Adjacent i j) :
    ∃ f : Fin 20, S ⊆ Set.range (faceVertex f) := by
  classical
  by_cases nonempty : S.Nonempty
  · obtain ⟨i, hi⟩ := nonempty
    by_cases second : ∃ j ∈ S, j ≠ i
    · obtain ⟨j, hj, hji⟩ := second
      by_cases third : ∃ k ∈ S, k ≠ i ∧ k ≠ j
      · obtain ⟨k, hk, hki, hkj⟩ := third
        obtain ⟨f, fi, fj, fk⟩ := exists_face_of_three i j k
          (.inr (adj i hi j hj hji.symm)) (.inr (adj i hi k hk hki.symm))
          (.inr (adj j hj k hk hkj.symm))
        have all : ∀ l : Fin 3, faceVertex f l ∈ S := by
          obtain ⟨a, ha⟩ := fi
          obtain ⟨b, hb⟩ := fj
          obtain ⟨c, hc⟩ := fk
          have ab : a ≠ b := fun eq => hji (hb.symm.trans ((congrArg _ eq).symm.trans ha))
          have ac : a ≠ c := fun eq => hki (hc.symm.trans ((congrArg _ eq).symm.trans ha))
          have bc : b ≠ c := fun eq => hkj (hc.symm.trans ((congrArg _ eq).symm.trans hb))
          have every : ∀ a b c l : Fin 3, a ≠ b → a ≠ c → b ≠ c → l = a ∨ l = b ∨ l = c := by
            decide +kernel
          intro l
          rcases every a b c l ab ac bc with rfl | rfl | rfl
          · exact ha.symm ▸ hi
          · exact hb.symm ▸ hj
          · exact hc.symm ▸ hk
        refine ⟨f, fun l hl => mem_face_of_adjacent f l (fun j => ?_)⟩
        exact or_iff_not_imp_left.mpr (adj l hl _ (all j))
      · obtain ⟨f, fi, fj, _⟩ := exists_face_of_three i j j
          (.inr (adj i hi j hj hji.symm)) (.inr (adj i hi j hj hji.symm)) (.inl rfl)
        refine ⟨f, fun l hl => ?_⟩
        by_cases li : l = i
        · exact li ▸ fi
        · have lj : l = j := by by_contra ne; exact third ⟨l, hl, li, ne⟩
          exact lj ▸ fj
    · obtain ⟨f, fi, _, _⟩ := exists_face_of_three i i i (.inl rfl) (.inl rfl) (.inl rfl)
      refine ⟨f, fun l hl => ?_⟩
      have li : l = i := by by_contra ne; exact second ⟨l, hl, ne⟩
      exact li ▸ fi
  · exact ⟨0, fun i hi => (nonempty ⟨i, hi⟩).elim⟩

theorem isClosed_hull : IsClosed hull :=
  (Set.finite_range rawVertex).isClosed_convexHull ℝ

private theorem faceTriangle_subset_hull (f : Fin 20) : faceTriangle f ⊆ hull :=
  convexHull_mono (by rintro _ ⟨i, rfl⟩; exact Set.mem_range_self _)

/-- Every hull point on a supporting plane is a combination of maximizing corners. -/
theorem mem_convexHull_maximizingCorners {n x : Space} {m : ℝ}
    (bound : ∀ i : Fin 12, inner ℝ n (rawVertex i) ≤ m)
    (hx : x ∈ hull) (eq : inner ℝ n x = m) :
    x ∈ convexHull ℝ (rawVertex '' {i | inner ℝ n (rawVertex i) = m}) := by
  classical
  change x ∈ convexHull ℝ (Set.range rawVertex) at hx
  rw [convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨s, w, nonneg, total, hx⟩ := hx
  rw [Finset.affineCombination_eq_linear_combination _ _ _ total] at hx
  have sum : ∑ i ∈ s, w i * inner ℝ n (rawVertex i) = m := by
    have map := congrArg (innerSL ℝ n) hx
    simpa only [map_sum, map_smul, innerSL_apply_apply, smul_eq_mul, eq] using map
  have zero : ∑ i ∈ s, w i * (m - inner ℝ n (rawVertex i)) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, total, sum, one_mul, sub_self]
  have vanishes (i : Fin 12) (hi : i ∈ s) (hne : inner ℝ n (rawVertex i) ≠ m) : w i = 0 :=
    ((mul_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun j hj =>
      mul_nonneg (nonneg j hj) (sub_nonneg.mpr (bound j))).mp zero i hi))).resolve_right
        (sub_ne_zero.mpr hne.symm)
  let t := s.filter fun i => inner ℝ n (rawVertex i) = m
  have htotal : ∑ i ∈ t, w i = 1 := by
    simpa only [← Finset.sum_subset (Finset.filter_subset _ _) (fun i hi hi' =>
      vanishes i hi (fun h => hi' (Finset.mem_filter.mpr ⟨hi, h⟩)))] using total
  have hsum : ∑ i ∈ t, w i • rawVertex i = x := by
    rw [Finset.sum_subset (Finset.filter_subset _ _) (fun i hi hi' => ?_)]
    · exact hx
    rw [vanishes i hi (fun h => hi' (Finset.mem_filter.mpr ⟨hi, h⟩)), zero_smul]
  rw [← hsum, ← Finset.centerMass_eq_of_sum_1 _ _ htotal]
  apply Finset.centerMass_mem_convexHull _ (fun i hi => nonneg i (Finset.mem_filter.mp hi).1)
    (htotal.symm ▸ zero_lt_one)
  intro i hi
  exact ⟨i, (Finset.mem_filter.mp hi).2, rfl⟩

theorem frontier_hull_subset_faces : frontier hull ⊆ ⋃ f : Fin 20, faceTriangle f := by
  intro x hx
  rw [frontier, isClosed_hull.closure_eq, Set.mem_sdiff] at hx
  obtain ⟨inHull, notInterior⟩ := hx
  obtain ⟨L, nonzero, support⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (convex_convexHull ℝ _) notInterior hull_interior_nonempty
  let n := (toDual ℝ Space).symm L
  have hn : n ≠ 0 := by
    intro eq
    exact nonzero ((toDual ℝ Space).symm.injective (eq.trans (map_zero _).symm))
  let m := inner ℝ n x
  have bound (i : Fin 12) : inner ℝ n (rawVertex i) ≤ m := by
    simpa only [m, n, toDual_symm_apply] using
      support _ (subset_convexHull ℝ _ (Set.mem_range_self i))
  obtain ⟨i, pos⟩ := exists_inner_rawVertex_pos hn
  have hm := pos.trans_le (bound i)
  obtain ⟨f, cover⟩ := exists_face_covering_clique fun _ hi _ hj hij =>
    adjacent_of_maximizers hm bound hij hi hj
  have sub : rawVertex '' {j | inner ℝ n (rawVertex j) = m} ⊆ Set.range (faceCorners f) := by
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨k, hk⟩ := cover hj
    exact ⟨k, congrArg rawVertex hk⟩
  exact Set.mem_iUnion.mpr ⟨f, convexHull_mono sub
    (mem_convexHull_maximizingCorners bound inHull rfl)⟩

end Unfoldings.FewestNets.Icosahedron
