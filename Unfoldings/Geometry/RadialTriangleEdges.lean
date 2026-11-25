module

public import Unfoldings.Basic
public import Unfoldings.Geometry.FrontierRays
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Radial chord triangles have exact cone coordinates and fill both sides of a paired edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Module

/-- A nonzero point is in the radial hull of a chord triangle exactly
when it has nonnegative coordinates in the triangle's linear basis. -/
theorem mem_positiveRadialHull_triangle_iff (b : Basis (Fin 3) ℝ Space) {x : Space} (nonzero : x ≠ 0) :
    x ∈ positiveRadialHull (convexHull ℝ (Set.range b)) ↔ ∀ i, 0 ≤ b.coord i x := by
  constructor
  · rintro ⟨q, positive, y, hy, rfl⟩ i
    let f := b.coord i
    have convex : Convex ℝ {p : Space | 0 ≤ f p} := convex_halfSpace_ge f.isLinear 0
    have sites : Set.range b ⊆ {p : Space | 0 ≤ f p} := by
      rintro _ ⟨j, rfl⟩
      change 0 ≤ b.repr (b j) i
      rw [b.repr_self]
      simp only [Finsupp.single_apply]; split <;> norm_num
    have lower : 0 ≤ f y := convexHull_min sites convex hy
    change 0 ≤ f (q • y)
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg positive.le lower
  · intro nonneg
    let s := ∑ i, b.coord i x
    have exists_pos : ∃ i, 0 < b.coord i x := by
      by_contra! none
      exact nonzero ((b.forall_coord_eq_zero_iff).mp
        (fun i => le_antisymm (none i) (nonneg i)))
    have positive : 0 < s := Finset.sum_pos' (fun i _ => nonneg i)
      (by obtain ⟨i, hi⟩ := exists_pos; exact ⟨i, Finset.mem_univ _, hi⟩)
    let weight (i : Fin 3) := b.coord i x / s
    let y := ∑ i, weight i • b i
    have in_hull : y ∈ convexHull ℝ (Set.range b) :=
      mem_convexHull_of_exists_fintype weight b
        (fun i => div_nonneg (nonneg i) positive.le)
        (by dsimp only [weight]; rw [← Finset.sum_div, div_self positive.ne'])
        (fun i => Set.mem_range_self i) rfl
    refine ⟨s, positive, y, in_hull, ?_⟩
    symm
    dsimp only [y, weight]
    simp_rw [Finset.smul_sum, smul_smul, ← mul_div_assoc, mul_div_cancel_left₀ _ positive.ne']
    exact b.sum_repr x

/-- All positive coordinates give an open neighborhood in the radial triangle. -/
theorem mem_interior_positiveRadialHull_triangle (b : Basis (Fin 3) ℝ Space) {x : Space}
    (positive : ∀ i, 0 < b.coord i x) :
    x ∈ interior (positiveRadialHull (convexHull ℝ (Set.range b))) := by
  let U : Set Space := ⋂ i : Fin 3, {z | 0 < b.coord i z}
  have open_U : IsOpen U := isOpen_iInter_of_finite
    (fun i => isOpen_lt continuous_const (b.coord i).continuous_of_finiteDimensional)
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (open_U.mem_nhds (Set.mem_iInter.mpr positive))
  intro z hz
  have pos (i : Fin 3) : 0 < b.coord i z := Set.mem_iInter.mp hz i
  have nz : z ≠ 0 := fun zero => by simpa only [zero, map_zero, lt_irrefl] using pos 0
  exact (mem_positiveRadialHull_triangle_iff b nz).mpr (fun i => (pos i).le)

/-- The coordinate transverse to a shared edge changes by an exact scalar. -/
theorem triangle_coord_two_of_common_edge (b c : Basis (Fin 3) ℝ Space)
    (first : b 0 = c 0) (last : b 1 = c 1) (x : Space) :
    b.coord 2 x = b.coord 2 (c 2) * c.coord 2 x := by
  have formula := b.sum_repr_mul_repr c x 2
  rw [Fin.sum_univ_three, ← first, ← last, b.repr_self, b.repr_self] at formula
  simpa [Basis.coord_apply, Finsupp.single_apply] using formula.symm

/-- The two triangles incident to an edge cover a full neighborhood of
every strict edge point if their opposite vertices are on opposite radial sides. -/
theorem mem_interior_radialTriangle_union_of_opposite {b c : Basis (Fin 3) ℝ Space}
    (first : b 0 = c 0) (last : b 1 = c 1) (opposite : b.coord 2 (c 2) < 0)
    {x : Space} (b₀ : 0 < b.coord 0 x) (b₁ : 0 < b.coord 1 x)
    (c₀ : 0 < c.coord 0 x) (c₁ : 0 < c.coord 1 x) :
    x ∈ interior (positiveRadialHull (convexHull ℝ (Set.range b)) ∪
      positiveRadialHull (convexHull ℝ (Set.range c))) := by
  let U : Set Space := {z | 0 < b.coord 0 z} ∩ {z | 0 < b.coord 1 z} ∩
    {z | 0 < c.coord 0 z} ∩ {z | 0 < c.coord 1 z}
  have open_U : IsOpen U := by
    have open_coord (d : Basis (Fin 3) ℝ Space) (i : Fin 3) :
        IsOpen {z : Space | 0 < d.coord i z} :=
      isOpen_lt continuous_const (d.coord i).continuous_of_finiteDimensional
    exact ((open_coord b 0).inter (open_coord b 1)).inter (open_coord c 0) |>.inter (open_coord c 1)
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (open_U.mem_nhds (show x ∈ U from ⟨⟨⟨b₀, b₁⟩, c₀⟩, c₁⟩))
  rintro z ⟨⟨⟨hb₀, hb₁⟩, hc₀⟩, hc₁⟩
  have nz : z ≠ 0 := fun zero => by
    change 0 < b.coord 0 z at hb₀
    simpa only [zero, map_zero, lt_irrefl] using hb₀
  rcases le_or_gt 0 (b.coord 2 z) with side | side
  · apply Or.inl ((mem_positiveRadialHull_triangle_iff b nz).mpr ?_)
    intro i
    fin_cases i
    · exact hb₀.le
    · exact hb₁.le
    · exact side
  · have side' : 0 ≤ c.coord 2 z := by
      by_contra! negative
      have both := mul_pos_of_neg_of_neg opposite negative
      exact side.not_ge ((triangle_coord_two_of_common_edge b c first last z).trans_gt both).le
    apply Or.inr ((mem_positiveRadialHull_triangle_iff c nz).mpr ?_)
    intro i
    fin_cases i
    · exact hc₀.le
    · exact hc₁.le
    · exact side'

end Unfoldings
