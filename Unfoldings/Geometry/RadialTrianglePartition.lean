module

public import Unfoldings.Geometry.RadialTriangleMultiplicity
public import Mathlib.Topology.Perfect
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-! A single weight-two witness certifies a finite spherical chord-triangle partition. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Module
open scoped Topology

local notation "Sphere" => Subtype (fun p : Space => p ∈ Metric.sphere (0 : Space) 1)

/-- The closed spherical section of a chord-triangle cone. -/
def chordTriangleOnSphere (b : Basis (Fin 3) ℝ Space) : Set Sphere :=
  {x | ∀ i, 0 ≤ b.coord i x.val}

/-- The strict spherical section, where all three coordinates are positive. -/
def strictChordTriangleOnSphere (b : Basis (Fin 3) ℝ Space) : Set Sphere :=
  {x | ∀ i, 0 < b.coord i x.val}

theorem isOpen_strictChordTriangleOnSphere (b : Basis (Fin 3) ℝ Space) :
    IsOpen (strictChordTriangleOnSphere b) := by
  have equal : strictChordTriangleOnSphere b = ⋂ i : Fin 3, {x : Sphere | 0 < b.coord i x.val} := by
    ext x
    rw [Set.mem_iInter]
    rfl
  rw [equal]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const
    ((b.coord i).continuous_of_finiteDimensional.comp continuous_subtype_val))

private theorem sphere3_perfect : PerfectSpace Sphere := by
  have dimension : 1 < Module.rank ℝ Space := by
    rw [← Module.finrank_eq_rank]
    norm_num [Space]
  let : ConnectedSpace Sphere :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere dimension 0 zero_le_one)
  have n : Nontrivial Sphere := by
    obtain ⟨v, norm_v⟩ := exists_norm_eq Space (zero_le_one : (0 : ℝ) ≤ 1)
    have first : v ∈ Metric.sphere (0 : Space) 1 := by
      rwa [Metric.mem_sphere, dist_zero_right]
    have last : -v ∈ Metric.sphere (0 : Space) 1 := by
      rwa [Metric.mem_sphere, dist_zero_right, norm_neg]
    refine ⟨⟨⟨v, first⟩, ⟨-v, last⟩, ?_⟩⟩
    intro same
    have equal : v = -v := congrArg Subtype.val same
    have doubled : (2 : ℝ) • v = 0 := by
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.mpr equal
    have zero : v = 0 := (smul_eq_zero.mp doubled).resolve_left (by norm_num)
    rw [zero, norm_zero] at norm_v
    exact zero_ne_one norm_v
  let := n
  infer_instance

/-- Once one regular point has exactly one sheet, the same paired mesh
covers the sphere and its positive faces have disjoint interiors. -/
theorem chordTriangle_partition_of_weight_two {I : Type*} [Fintype I] [Nonempty I]
    (b : I → Basis (Fin 3) ℝ Space) (sites : ∀ i j, ‖b i j‖ = 1)
    (mate : I × Fin 3 → I × Fin 3) (involutive : Function.Involutive mate)
    (preserves_edge : ∀ e p, OnOpenRadialEdge (b e.1) e.2 p →
      OnOpenRadialEdge (b (mate e).1) (mate e).2 p)
    (opposite : ∀ e, ∃ c < (0 : ℝ), ∀ q,
      (b e.1).coord e.2 q = c * (b (mate e).1).coord (mate e).2 q)
    (witness : Sphere) (regular : ∀ i j, witness.val ≠ b i j)
    (one_sheet : (∑ i, radialTriangleWeight (b i) witness.val) = 2) :
    (⋃ i, chordTriangleOnSphere (b i)) = Set.univ ∧
      Pairwise fun i j => Disjoint (strictChordTriangleOnSphere (b i))
        (strictChordTriangleOnSphere (b j)) := by
  classical
  have exactly_two (x : Sphere) (outside : ∀ i j, x.val ≠ b i j) :
      (∑ i, radialTriangleWeight (b i) x.val) = 2 :=
    (radialTriangleWeight_sum_eq b sites mate involutive preserves_edge opposite
      x witness outside regular).trans one_sheet
  constructor
  · apply Set.eq_univ_of_forall
    intro x
    by_cases at_vertex : ∃ i j, x.val = b i j
    · obtain ⟨i, j, equal⟩ := at_vertex
      apply Set.mem_iUnion.mpr
      refine ⟨i, fun k => ?_⟩
      rw [equal, Basis.coord_apply, (b i).repr_self]
      simp only [Finsupp.single_apply]; split <;> norm_num
    · push Not at at_vertex
      by_contra none
      have zero (i : I) : radialTriangleWeight (b i) x.val = 0 := by
        have weak : ¬ ∀ k, 0 ≤ (b i).coord k x.val :=
          fun h => none (Set.mem_iUnion.mpr ⟨i, h⟩)
        have strict : ¬ ∀ k, 0 < (b i).coord k x.val := fun h => weak (fun k => (h k).le)
        simp only [radialTriangleWeight, ite_eq_right strict, ite_eq_right weak]
      have impossible := exactly_two x at_vertex
      simp only [zero, Finset.sum_const_zero] at impossible
      norm_num at impossible
  · intro i j different
    rw [Set.disjoint_left]
    intro x hi hj
    let vertices : Set Sphere := Set.range fun ij : I × Fin 3 =>
      ⟨b ij.1 ij.2, Metric.mem_sphere.mpr ((dist_zero_right _).trans (sites ij.1 ij.2))⟩
    let U := strictChordTriangleOnSphere (b i) ∩ strictChordTriangleOnSphere (b j)
    have opened : IsOpen U := (isOpen_strictChordTriangleOnSphere _).inter
      (isOpen_strictChordTriangleOnSphere _)
    let : PerfectSpace Sphere := sphere3_perfect
    have some_regular : ∃ y ∈ U, y ∉ vertices := by
      by_contra! all
      exact infinite_of_mem_nhds x (opened.mem_nhds ⟨hi, hj⟩)
        ((Set.finite_range _ : vertices.Finite).subset all)
    obtain ⟨y, hy, avoids⟩ := some_regular
    have outside (p : I) (q : Fin 3) : y.val ≠ b p q :=
      fun equal => avoids ⟨(p, q), Subtype.ext equal.symm⟩
    have wi : radialTriangleWeight (b i) y.val = 2 := ite_eq_left hy.1
    have wj : radialTriangleWeight (b j) y.val = 2 := ite_eq_left hy.2
    have at_least := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun i => radialTriangleWeight (b i) y.val)
      (Finset.subset_univ ({i, j} : Finset I)) (fun _ _ _ => Nat.zero_le _)
    simp only [Finset.sum_insert (show i ∉ ({j} : Finset I) by simpa using different),
      Finset.sum_singleton, wi, wj, exactly_two y outside] at at_least
    omega

end Unfoldings
