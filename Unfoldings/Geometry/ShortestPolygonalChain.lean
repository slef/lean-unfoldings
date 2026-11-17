module

public import Unfoldings.Geometry.PolygonalLength
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Module

/-! A polygonal chain attaining its Euclidean chord length keeps exact directed arclength. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} (P : PolygonalChain E n)

/-- Equality in the whole triangle inequality fixes every directed edge, including
zero edges. The scalar is its true fraction of the nonzero chord length. -/
theorem edge_eq_chord_scale_of_length_eq
    (different : P.vertex (Fin.last n) ≠ P.vertex 0)
    (shortest : P.projectedLength = ‖P.vertex (Fin.last n) - P.vertex 0‖) (i : Fin n) :
    P.edge i = (‖P.edge i‖ / ‖P.vertex (Fin.last n) - P.vertex 0‖) •
      (P.vertex (Fin.last n) - P.vertex 0) := by
  classical
  let d := P.vertex (Fin.last n) - P.vertex 0
  have nonnegative (j : Fin n) (_ : j ∈ (Finset.univ : Finset (Fin n))) :
      0 ≤ ‖d‖ * ‖P.edge j‖ - inner ℝ d (P.edge j) :=
    sub_nonneg.mpr (real_inner_le_norm d (P.edge j))
  have total : (∑ j : Fin n, (‖d‖ * ‖P.edge j‖ - inner ℝ d (P.edge j))) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← inner_sum, P.sum_edge]
    change ‖d‖ * P.projectedLength - inner ℝ d d = 0
    rw [shortest, real_inner_self_eq_norm_sq]
    ring
  have at_i := (Finset.sum_eq_zero_iff_of_nonneg nonnegative).mp total i (Finset.mem_univ _)
  exact ((inner_eq_norm_mul_iff_div (𝕜 := ℝ) (sub_ne_zero.mpr different)).mp
    (sub_eq_zero.mp at_i).symm).symm

/-- Every shortest polygonal chain vertex lies at its exact cumulative arclength
on the directed chord. This retains the original direction without any angle choice. -/
theorem vertex_eq_chord_arclength_of_length_eq
    (different : P.vertex (Fin.last n) ≠ P.vertex 0)
    (shortest : P.projectedLength = ‖P.vertex (Fin.last n) - P.vertex 0‖)
    (i : Fin (n + 1)) :
    P.vertex i = P.vertex 0 +
      (Fin.partialSum (fun j => ‖P.edge j‖) i / ‖P.vertex (Fin.last n) - P.vertex 0‖) •
        (P.vertex (Fin.last n) - P.vertex 0) := by
  induction i using Fin.induction with
  | zero => rw [Fin.partialSum_zero, zero_div, zero_smul, add_zero]
  | succ k previous =>
    rw [Fin.partialSum_succ, add_div, add_smul,
      ← P.edge_eq_chord_scale_of_length_eq different shortest k]
    change P.vertex k.succ = _ + (_ + (P.vertex k.succ - P.vertex k.castSucc))
    rw [← add_assoc, ← previous]
    abel

end Unfoldings.PolygonalChain
