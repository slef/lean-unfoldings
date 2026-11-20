module

public import Unfoldings.Convex.FiniteNormalFan
public import Unfoldings.Geometry.AffineMaximum
public import Mathlib.Analysis.Convex.Join
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! Full-dimensional normal cones are exactly those at extreme sites. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open MeasureTheory

variable {I : Type*} [Finite I] {site : I → Space} (different : Function.Injective site)
  (i : I)

private theorem strict_support_of_notMem_other_hull
    (outside : site i ∉ convexHull ℝ (site '' {i}ᶜ)) :
    ∃ n : Space, ∀ j ≠ i, inner ℝ n (site j) < inner ℝ n (site i) := by
  have closed := ((Set.toFinite ({i}ᶜ : Set I)).image site).isCompact_convexHull ℝ
  obtain ⟨f, c, smaller, larger⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull ℝ _) closed.isClosed outside
  let n := (InnerProductSpace.toDual ℝ Space).symm f
  have evaluate (x : Space) : inner ℝ n x = f x := by
    change (InnerProductSpace.toDual ℝ Space n) x = f x
    rw [LinearIsometryEquiv.apply_symm_apply]
  exact ⟨n, fun j ji => by
    rw [evaluate, evaluate]
    exact (smaller _ (subset_convexHull ℝ _ ⟨j, ji, rfl⟩)).trans larger⟩

omit [Finite I] in
private theorem notMem_other_hull_of_strict_support {n : Space}
    (support : ∀ j ≠ i, inner ℝ n (site j) < inner ℝ n (site i)) :
    site i ∉ convexHull ℝ (site '' {i}ᶜ) := by
  have contained : convexHull ℝ (site '' {i}ᶜ) ⊆ {x | inner ℝ n x < inner ℝ n (site i)} :=
    convexHull_min (by rintro _ ⟨j, hj, rfl⟩; exact support j hj)
      (convex_halfSpace_lt (innerSL ℝ n).toLinearMap.isLinear _)
  intro present
  have impossible : inner ℝ n (site i) < inner ℝ n (site i) := contained present
  exact (lt_irrefl _) impossible

include different

theorem mem_interior_finiteHullNormalCone_iff {n : Space} :
    n ∈ interior (finiteHullNormalCone site i) ↔
      ∀ j ≠ i, inner ℝ n (site j) < inner ℝ n (site i) := by
  constructor
  · intro h j ji
    let f := innerSL ℝ (site j - site i)
    have fne : f ≠ 0 := by
      intro zero
      have value := DFunLike.congr_fun zero (site j - site i)
      change inner ℝ (site j - site i) (site j - site i) = 0 at value
      exact ji (different (sub_eq_zero.mp (inner_self_eq_zero.mp value)))
    have bound (x : Space) (hx : x ∈ finiteHullNormalCone site i) : f x ≤ 0 := by
      change inner ℝ (site j - site i) x ≤ 0
      rw [real_inner_comm x, inner_sub_right, sub_nonpos]
      exact hx j
    have strict := supporting_functional_lt_on_interior f fne _ 0 bound n h
    change inner ℝ (site j - site i) n < 0 at strict
    rwa [real_inner_comm n, inner_sub_right, sub_lt_zero] at strict
  · intro h
    let good := ⋂ j : {j : I // j ≠ i}, {x : Space | inner ℝ x (site j) < inner ℝ x (site i)}
    have op : IsOpen good :=
      isOpen_iInter_of_finite (fun j =>
        isOpen_lt (continuous_id.inner continuous_const) (continuous_id.inner continuous_const))
    apply mem_interior_iff_mem_nhds.mpr
    refine Filter.mem_of_superset (op.mem_nhds (Set.mem_iInter.mpr fun j => h j j.property)) ?_
    intro x hx j
    by_cases same : j = i
    · rw [same]
    · exact (Set.mem_iInter.mp hx ⟨j, same⟩).le

/-- A site of a finite hull is extreme exactly when it lies outside the hull of
the other sites. -/
theorem finiteHull_extreme_iff_notMem_other_hull :
    site i ∈ (convexHull ℝ (Set.range site)).extremePoints ℝ ↔
      site i ∉ convexHull ℝ (site '' {i}ᶜ) := by
  let H := convexHull ℝ (Set.range site)
  have mem_i : site i ∈ H := subset_convexHull ℝ _ ⟨i, rfl⟩
  rw [(convex_convexHull ℝ _).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff]
  constructor
  · intro extreme member
    apply extreme.2
    apply convexHull_mono _ member
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨subset_convexHull ℝ _ ⟨j, rfl⟩, fun eq => hj (different eq)⟩
  · intro outside
    obtain ⟨n, strict⟩ := strict_support_of_notMem_other_hull i outside
    refine ⟨mem_i, ?_⟩
    have h_other (x : Space) (hx : x ∈ H) (x_ne : x ≠ site i) :
        inner ℝ n x < inner ℝ n (site i) := by
      have source : Set.range site = insert (site i) (site '' {i}ᶜ) := by
        ext p
        simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_image,
          Set.mem_compl_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨j, rfl⟩
          by_cases equal : j = i
          · exact Or.inl (congrArg site equal)
          · exact Or.inr ⟨j, equal, rfl⟩
        · rintro (rfl | ⟨j, _, rfl⟩)
          · exact ⟨i, rfl⟩
          · exact ⟨j, rfl⟩
      change x ∈ convexHull ℝ (Set.range site) at hx
      rw [source] at hx
      by_cases ne : (site '' {i}ᶜ).Nonempty
      · rw [convexHull_insert ne, convexJoin_singleton_left] at hx
        obtain ⟨z, z_in, hz⟩ := Set.mem_iUnion₂.mp hx
        have z_lt : inner ℝ n z < inner ℝ n (site i) := by
          apply convexHull_min _ (convex_halfSpace_lt (innerSL ℝ n).toLinearMap.isLinear _) z_in
          rintro _ ⟨j, hj, rfl⟩
          exact strict j hj
        obtain ⟨a, b, ha, hb, hab, expr⟩ := hz
        have hb_pos : 0 < b := by
          by_contra hn
          have zero : b = 0 := le_antisymm (le_of_not_gt hn) hb
          have one : a = 1 := by linarith
          exact x_ne (by simpa [one, zero] using expr.symm)
        rw [← expr, inner_add_right, real_inner_smul_right, real_inner_smul_right]
        have equal := congrArg (fun t : ℝ => t * inner ℝ n (site i)) hab
        nlinarith only [mul_lt_mul_of_pos_left z_lt hb_pos, equal]
      · rw [Set.not_nonempty_iff_eq_empty.mp ne, insert_empty_eq, convexHull_singleton] at hx
        exact (x_ne hx).elim
    have hs : H \ {site i} ⊆ {x | inner ℝ n x < inner ℝ n (site i)} :=
      fun x hx => h_other x hx.1 hx.2
    have hull := convexHull_min hs (convex_halfSpace_lt (innerSL ℝ n).toLinearMap.isLinear _)
    intro member
    have impossible : inner ℝ n (site i) < inner ℝ n (site i) := hull member
    exact (lt_irrefl _) impossible

/-- The normal cone has nonempty ambient interior exactly at an extreme
point of the hull of the given finite sites. -/
theorem interior_finiteHullNormalCone_nonempty_iff :
    (interior (finiteHullNormalCone site i)).Nonempty ↔
      site i ∈ (convexHull ℝ (Set.range site)).extremePoints ℝ := by
  rw [finiteHull_extreme_iff_notMem_other_hull different i]
  constructor
  · rintro ⟨n, hn⟩
    exact notMem_other_hull_of_strict_support i
      ((mem_interior_finiteHullNormalCone_iff different i).mp hn)
  · intro h
    obtain ⟨n, support⟩ := strict_support_of_notMem_other_hull i h
    exact ⟨n, (mem_interior_finiteHullNormalCone_iff different i).mpr support⟩

/-- Every normal cone at a subdivision site lies in a finite union of
null tying planes. -/
theorem solidAngle_finiteHullNormalCone_eq_zero_of_not_extreme
    (nonextreme : site i ∉ (convexHull ℝ (Set.range site)).extremePoints ℝ) :
    solidAngleMeasure (finiteHullNormalCone site i) = 0 := by
  let tie (j : {j : I // j ≠ i}) :=
    {w : Space | inner ℝ (site (j : I) - site i) w = 0}
  have covered : finiteHullNormalCone site i ⊆ ⋃ j, tie j := by
    intro w hw
    have h : w ∉ interior (finiteHullNormalCone site i) := fun interior =>
      nonextreme ((interior_finiteHullNormalCone_nonempty_iff different i).mp ⟨w, interior⟩)
    rw [mem_interior_finiteHullNormalCone_iff different i] at h
    push Not at h
    obtain ⟨j, ji, ge⟩ := h
    apply Set.mem_iUnion.mpr
    refine ⟨⟨j, ji⟩, ?_⟩
    change inner ℝ (site j - site i) w = 0
    rw [real_inner_comm w, inner_sub_right, sub_eq_zero]
    exact le_antisymm (hw j) ge
  have null (j : {j : I // j ≠ i}) : solidAngleMeasure (tie j) = 0 := by
    let f := innerSL ℝ (site (j : I) - site i)
    have fne : f ≠ 0 := by
      intro zero
      have h := DFunLike.congr_fun zero (site (j : I) - site i)
      change inner ℝ (site (j : I) - site i) (site (j : I) - site i) = 0 at h
      exact j.property (different (sub_eq_zero.mp (inner_self_eq_zero.mp h)))
    exact solidAngleMeasure_ker f fne
  exact measure_mono_null covered (measure_iUnion_null_iff.mpr null)

end Unfoldings
