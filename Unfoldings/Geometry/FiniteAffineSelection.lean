module

public import Unfoldings.Geometry.AffineArrangement
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Connected.Clopen

/-!
# Continuous selections from finitely many affine maps

Distinct affine maps have coincidence sets contained in a proper affine
hyperplane. On a connected set avoiding these hyperplanes, a continuous
selection from the finite family must use one affine map throughout.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem exists_affine_coincidence_equation (A B : E →ᵃ[ℝ] V) (different : A ≠ B) :
    ∃ l : E →ᵃ[ℝ] ℝ, l ≠ 0 ∧ ∀ x, A x = B x → l x = 0 := by
  have exists_point : ∃ x, A x ≠ B x := by
    by_contra all
    exact different (AffineMap.ext (fun x => not_not.mp (not_exists.mp all x)))
  obtain ⟨x, hx⟩ := exists_point
  let v := A x - B x
  let l := (innerₛₗ ℝ v).toAffineMap.comp (A - B)
  have positive : 0 < l x := by
    change 0 < inner ℝ v v
    exact real_inner_self_pos.mpr (sub_ne_zero.mpr hx)
  refine ⟨l, ?_, ?_⟩
  · intro zero
    have at_x := congrArg (fun f : E →ᵃ[ℝ] ℝ => f x) zero
    exact positive.ne' at_x
  · intro y equal
    change inner ℝ v (A y - B y) = 0
    rw [equal, sub_self, inner_zero_right]

variable [FiniteDimensional ℝ E]

theorem finite_affine_selection_constant {X ι : Type*} [TopologicalSpace X]
    [ConnectedSpace X] [Finite ι] (maps : ι → E →ᵃ[ℝ] V)
    (coordinate : X → E) (continuous_coordinate : Continuous coordinate)
    (value : X → V) (continuous_value : Continuous value)
    (selects : ∀ x, ∃ i, value x = maps i (coordinate x))
    (separated : ∀ x i j, maps i ≠ maps j → maps i (coordinate x) ≠ maps j (coordinate x)) :
    ∃ i, ∀ x, value x = maps i (coordinate x) := by
  classical
  let x : X := Classical.choice inferInstance
  obtain ⟨i, at_x⟩ := selects x
  let chosen := {x | value x = maps i (coordinate x)}
  let other := ⋃ j : {j : ι // maps j ≠ maps i}, {x | value x = maps j.val (coordinate x)}
  have closed_chosen : IsClosed chosen := isClosed_eq continuous_value
    ((maps i).continuous_of_finiteDimensional.comp continuous_coordinate)
  have closed_other : IsClosed other := isClosed_iUnion_of_finite (fun j =>
    isClosed_eq continuous_value ((maps j.val).continuous_of_finiteDimensional.comp
      continuous_coordinate))
  have complement : chosen = otherᶜ := by
    ext y
    constructor
    · intro equal member
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp member
      exact separated y j.val i j.property (hj.symm.trans equal)
    · intro outside
      obtain ⟨j, hj⟩ := selects y
      by_cases same : maps j = maps i
      · exact hj.trans (congrArg (fun A : E →ᵃ[ℝ] V => A (coordinate y)) same)
      · exact (outside (Set.mem_iUnion.mpr ⟨⟨j, same⟩, hj⟩)).elim
  have all : chosen = Set.univ :=
    IsClopen.eq_univ ⟨closed_chosen, complement ▸ closed_other.isOpen_compl⟩ ⟨x, at_x⟩
  refine ⟨i, ?_⟩
  intro y
  change y ∈ chosen
  rw [all]
  exact Set.mem_univ y

omit [FiniteDimensional ℝ E] in
theorem exists_finite_affine_coincidence_equations {ι : Type*} [Finite ι]
    (maps : ι → E →ᵃ[ℝ] V) :
    ∃ L : Set (E →ᵃ[ℝ] ℝ), L.Finite ∧ (∀ l ∈ L, l ≠ 0) ∧
      ∀ i j, maps i ≠ maps j → ∀ x, maps i x = maps j x → ∃ l ∈ L, l x = 0 := by
  classical
  have equations (p : ι × ι) : ∃ l : E →ᵃ[ℝ] ℝ,
      l ≠ 0 ∧ ∀ x, maps p.1 ≠ maps p.2 → maps p.1 x = maps p.2 x → l x = 0 := by
    by_cases same : maps p.1 = maps p.2
    · exact ⟨AffineMap.const ℝ E 1, by
        intro zero
        have equal := congrArg (fun f : E →ᵃ[ℝ] ℝ => f 0) zero
        simp at equal, fun _ different => (different same).elim⟩
    · obtain ⟨l, nonzero, vanishes⟩ := exists_affine_coincidence_equation (maps p.1) (maps p.2) same
      exact ⟨l, nonzero, fun x _ => vanishes x⟩
  choose equation nonzero vanishes using equations
  refine ⟨Set.range equation, Set.finite_range _, ?_, ?_⟩
  · rintro l ⟨p, rfl⟩
    exact nonzero p
  · intro i j different x equal
    exact ⟨equation (i, j), ⟨(i, j), rfl⟩, vanishes (i, j) x different equal⟩

end Unfoldings
