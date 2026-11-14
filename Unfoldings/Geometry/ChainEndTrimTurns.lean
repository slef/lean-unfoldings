module

public import Unfoldings.Geometry.ChainEndTrimming
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-! Genuine endpoint trimming preserves every original bank direction and corner turn. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E (n + 2))

/-- Trimming strictly inside both terminal links changes lengths but no normalized direction. -/
theorem normalize_trimEnds_edge (a b : unitInterval) (first : (a : ℝ) < 1) (last : 0 < (b : ℝ))
    (i : Fin (n + 2)) :
    NormedSpace.normalize ((P.trimEnds a b).edge i) = NormedSpace.normalize (P.edge i) := by
  rw [P.trimEnds_edge]
  apply NormedSpace.normalize_smul_of_pos
  split_ifs <;> linarith

/-- Every intermediate actual corner has exactly its original turning angle. -/
theorem angle_trimEnds_edges (a b : unitInterval) (first : (a : ℝ) < 1) (last : 0 < (b : ℝ))
    (i j : Fin (n + 2)) :
    InnerProductGeometry.angle ((P.trimEnds a b).edge i) ((P.trimEnds a b).edge j) =
      InnerProductGeometry.angle (P.edge i) (P.edge j) := by
  rw [← InnerProductGeometry.angle_normalize_left, ← InnerProductGeometry.angle_normalize_right,
    P.normalize_trimEnds_edge a b first last i, P.normalize_trimEnds_edge a b first last j,
    InnerProductGeometry.angle_normalize_left, InnerProductGeometry.angle_normalize_right]

/-- Exact complex speed and real-heading factors survive corresponding endpoint trimming. -/
theorem trimEnds_complex_edge_factor (P Q : PolygonalChain ℂ (n + 2))
    (factor : Fin (n + 2) → ℂ) (edges : ∀ i, Q.edge i = factor i * P.edge i)
    (a b : unitInterval) (i : Fin (n + 2)) :
    (Q.trimEnds a b).edge i = factor i * (P.trimEnds a b).edge i := by
  rw [Q.trimEnds_edge, P.trimEnds_edge, edges, Complex.real_smul, Complex.real_smul]
  ring

end Unfoldings.PolygonalChain
