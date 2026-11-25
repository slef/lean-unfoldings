module

public import Unfoldings.Roof.ProjectedGermSegments
public import Unfoldings.Roof.GraphWindowFaces
public import Unfoldings.Geometry.GraphWindowLine
public import Unfoldings.Polyhedron.ProjectedBoundaryChain

/-! Both physical sides of a trimmed forward bank are determined by original edge orientations. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open PlanarTopology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem projectedBoundaryChain_start_germ {retain : Set C.Seam} {n : ℕ}
    (chain : (C.boundarySystem retain).Chain n) (i : Fin (n + 1)) :
    (K.folding.projectedBoundaryChain chain).vertex i.castSucc =
      K.projectedGermStart (chain.point i).val := by
  rw [K.folding.projectedBoundaryChain_vertex_castSucc, K.folding.boundaryPosition_raw]
  rfl

theorem projectedBoundaryChain_finish_germ {retain : Set C.Seam} {n : ℕ}
    (chain : (C.boundarySystem retain).Chain n) (i : Fin (n + 1)) :
    (K.folding.projectedBoundaryChain chain).vertex i.succ =
      K.projectedGermFinish (chain.point i).val := by
  have forward := K.folding.projectedBoundaryChain_edge chain i
  have left := K.projectedBoundaryChain_start_germ chain i
  change (K.folding.projectedBoundaryChain chain).vertex i.succ -
    (K.folding.projectedBoundaryChain chain).vertex i.castSucc =
      Cap.horizontal (K.folding.germFarPoint (chain.point i).val -
      K.folding.place (chain.point i).val.1.1 ((C.triangle (chain.point i).val.1.1).vertex
        (chain.point i).val.1.2)) at forward
  rw [left, map_sub] at forward
  exact sub_left_injective forward

private theorem orient_of_lineMap_pair (a b x : Plane) (u v : ℝ) :
    orient (AffineMap.lineMap a b u) (AffineMap.lineMap a b v) x =
      (v - u) * orient a b x := by
  simp only [AffineMap.lineMap_apply_module', orient, PiLp.sub_apply, PiLp.smul_apply,
    PiLp.add_apply, smul_eq_mul]
  ring

variable {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
  (aligned : ∀ j, Disjoint (interior (K.projectedTriangle j).carrier) (graphPoint f '' Set.Icc a b))

include hf aligned in
/-- Membership of an actual original face on the upper bank is its signed
area in the forward direction of any genuine subsegment of that edge. -/
theorem graphWindowFace_iff_germ_orientation (p : C.Germ) (u v : unitInterval) {r s : Plane}
    (first : r = AffineMap.lineMap (K.projectedGermStart p) (K.projectedGermFinish p) u.val)
    (last : s = AffineMap.lineMap (K.projectedGermStart p) (K.projectedGermFinish p) v.val)
    (forward : r 0 < s 0) (trace : segment ℝ r s ⊆ graphPoint f '' Set.Icc a b) :
    p.1.1 ∈ K.graphWindowFaces f a b ↔ 0 < (v.val - u.val) * K.projectedGermOrientation p := by
  let T := K.projectedTriangle p.1.1
  have edge (z : Plane) (t : unitInterval)
      (position : z = AffineMap.lineMap (K.projectedGermStart p) (K.projectedGermFinish p) t.val) :
      z ∈ T.carrier := by
    apply T.edge_subset (C.germEdge p).edge
    rw [← K.projectedGerm_segment_eq, position]
    exact lineMap_mem_segment ℝ _ _ t.property
  obtain ⟨z, hz, above⟩ := interiorAboveGraph_iff_orient_of_midpoint hf T.convex_carrier
    T.interior_nonempty (aligned p.1.1) forward trace
    (T.convex_carrier.midpoint_mem (edge r u first) (edge s v last))
  change (p.1.1 ∈ K.graphWindowFaces f a b) ↔ _ at above ⊢
  refine above.trans ?_
  rw [first, last, orient_of_lineMap_pair]
  have nonzero : v.val - u.val ≠ 0 := by
    intro zero
    have equal : v.val = u.val := sub_eq_zero.mp zero
    have position : s = r := last.trans (equal ▸ first.symm)
    exact forward.ne (congrArg (fun z : Plane => z 0) position.symm)
  have side := K.projectedGerm_interior_orientation_mul_pos p hz
  have both :
      0 < ((v.val - u.val) * orient (K.projectedGermStart p) (K.projectedGermFinish p) z) *
        ((v.val - u.val) * K.projectedGermOrientation p) := by
    calc
      _ = (v.val - u.val) ^ 2 * (K.projectedGermOrientation p *
        orient (K.projectedGermStart p) (K.projectedGermFinish p) z) := by ring
      _ > 0 := mul_pos (sq_pos_of_ne_zero nonzero) side
  exact pos_iff_pos_of_mul_pos both

include hf aligned in
/-- A positive forward bank selects its own face and excludes the other physical bank face. -/
theorem graphWindowFaces_on_positive_germ (p : C.Germ) (u v : unitInterval) (ordered : u.val < v.val)
    {r s : Plane}
    (first : r = AffineMap.lineMap (K.projectedGermStart p) (K.projectedGermFinish p) u.val)
    (last : s = AffineMap.lineMap (K.projectedGermStart p) (K.projectedGermFinish p) v.val)
    (forward : r 0 < s 0) (trace : segment ℝ r s ⊆ graphPoint f '' Set.Icc a b)
    (orientation : 0 < K.projectedGermOrientation p)
    (internal : ¬ C.IsBoundaryEdge Set.univ (C.germEdge p)) :
    p.1.1 ∈ K.graphWindowFaces f a b ∧ (C.mateGerm Set.univ p).1.1 ∉ K.graphWindowFaces f a b := by
  have span : 0 < v.val - u.val := sub_pos.mpr ordered
  refine ⟨(K.graphWindowFace_iff_germ_orientation hf aligned p u v first last forward trace).mpr
    (mul_pos span orientation), ?_⟩
  have sign : K.projectedGermOrientation (C.mateGerm Set.univ p) < 0 := by
    rcases mul_neg_iff.mp (K.projectedGermOrientation_mate_mul_neg p internal) with
      ⟨_, impossible⟩ | ⟨negative, _⟩
    · exact (orientation.not_gt impossible).elim
    · exact negative
  apply (K.graphWindowFace_iff_germ_orientation hf aligned (C.mateGerm Set.univ p) u v
    (by rwa [K.projectedGermStart_mate, K.projectedGermFinish_mate])
    (by rwa [K.projectedGermStart_mate, K.projectedGermFinish_mate]) forward trace).not.mpr
  exact (mul_neg_of_pos_of_neg span sign).not_gt

end Unfoldings.ConvexRoof
