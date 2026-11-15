module

public import Unfoldings.Geometry.RadialRayVertices
public import Unfoldings.Geometry.PolygonalRayFrame
public import Unfoldings.Geometry.ChainSplit

/-! Source-relative coordinates and strict terminal progress of original bank edges. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (R : PolygonalRay E n)

/-- A genuine outward edge has strictly positive radial progress at its terminal vertex,
even when its initial radial progress vanishes. -/
theorem inner_terminal_edge_pos (outward : R.Outward) (i : Fin n)
    (genuine : R.chain.vertex i.castSucc ≠ R.chain.vertex i.succ) :
    0 < inner ℝ (R.chain.vertex i.succ - R.start)
      (R.chain.vertex i.succ - R.chain.vertex i.castSucc) := by
  have initial := (monotone_dist_lineMap_iff R.start (R.chain.vertex i.castSucc)
    (R.chain.vertex i.succ)).mp (outward.1 i (Nat.zero_le _))
  have nonzero : R.chain.vertex i.succ - R.chain.vertex i.castSucc ≠ 0 :=
    sub_ne_zero.mpr genuine.symm
  have positive := sq_pos_of_pos (norm_pos_iff.mpr nonzero)
  have difference : R.chain.vertex i.succ - R.start =
      (R.chain.vertex i.castSucc - R.start) +
        (R.chain.vertex i.succ - R.chain.vertex i.castSucc) := by abel
  rw [difference, inner_add_left, real_inner_self_eq_norm_sq]
  linarith

/-- Every original vertex is on the actual bank, independently of its parametrization. -/
theorem vertex_mem_carrier (i : Fin (n + 1)) : R.chain.vertex i ∈ R.carrier :=
  Or.inl (R.chain.vertex_mem_path_range i)

variable {m : ℕ} (P : PolygonalRay ℂ m) (outward : P.Outward) (nonzero : P.direction ≠ 0)

/-- The radius coordinate selects the original physical point, not an extrapolation. -/
theorem radialPoint_norm_eq_of_mem {p : ℂ} (member : p ∈ P.carrier) :
    P.radialPoint outward nonzero ‖p - P.start‖₊ = p := by
  apply P.eq_of_radius_eq outward nonzero (P.radialPoint_mem outward nonzero _) member
  rw [dist_eq_norm', dist_eq_norm', P.norm_radialPoint_sub_start]
  rfl

/-- At a named vertex the intrinsic bank radius recovers its exact original coordinates. -/
theorem radialPoint_vertex (i : Fin (m + 1)) :
    P.radialPoint outward nonzero ‖P.chain.vertex i - P.start‖₊ = P.chain.vertex i :=
  P.radialPoint_norm_eq_of_mem outward nonzero (P.vertex_mem_carrier i)

end Unfoldings.PolygonalRay
