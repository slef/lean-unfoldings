module

public import Unfoldings.Cap.ProjectedSignedBankRays

/-! An interior projected directed ray determines its original edge and both possible face sides. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {w : C.Vertex Set.univ}

/-- Every original link prefix keeps its occupied side, including negative orientations. -/
theorem projected_link_chain_orientation_product {n : ℕ}
    (c : (C.linkSystem Set.univ w).Chain n) (i : Fin (n + 1)) :
    0 < K.projectedGermOrientation (c.point i).val * K.projectedGermOrientation c.first.val := by
  have same := K.projected_chain_orientation_sign c i
  rcases lt_or_gt_of_ne (K.projectedGermOrientation_ne_zero c.first.val) with negative | positive
  · have last : K.projectedGermOrientation (c.point i).val < 0 :=
      lt_of_le_of_ne (le_of_not_gt (fun h => negative.not_gt (same.mp h)))
        (K.projectedGermOrientation_ne_zero _)
    exact mul_pos_of_neg_of_neg last negative
  · exact mul_pos (same.mpr positive) positive

/-- Across any original interior seam germ, the incident face is on the other occupied side. -/
theorem projected_linkMate_orientation_product (internal : ¬ C.IsBoundaryVertex Set.univ w)
    (p : C.LinkGerm Set.univ w) :
    K.projectedGermOrientation (C.linkMate Set.univ w p).val *
      K.projectedGermOrientation p.val < 0 := by
  have free (q : C.LinkGerm Set.univ w) : C.linkMate Set.univ w q ≠ q := fun fixed =>
    internal ((C.isBoundaryVertex_iff_linkMate_fixed Set.univ w).mpr ⟨q, fixed⟩)
  obtain ⟨n, c, first, closes, _covers⟩ := (C.linkSystem Set.univ w).exists_cycle_chain
    (C.linkSystem_connected Set.univ w) free p
  have same := K.projected_link_chain_orientation_product c (Fin.last n)
  change C.linkMate Set.univ w (C.linkTurn Set.univ w c.last) = c.first at closes
  have pairing : C.linkMate Set.univ w c.first = C.linkTurn Set.univ w c.last := by
    rw [← closes, C.linkMate_involutive]
  rw [first] at pairing
  have raw : (C.linkMate Set.univ w p).val = C.turnGerm c.last.val :=
    congrArg Subtype.val pairing
  rw [raw, K.projectedGermOrientation_turn]
  change 0 < K.projectedGermOrientation c.last.val * K.projectedGermOrientation c.first.val at same
  rw [first] at same
  linarith

/-- A physical directed ray at an interior vertex has just its two original incident germs.
The vector may initially be specified with any positive scale. -/
theorem projected_raw_germ_eq_or_mate_of_positive_scale (p q : C.Germ)
    (apex : (K.projectedTriangle p.1.1).vertex p.1.2 =
      (K.projectedTriangle q.1.1).vertex q.1.2)
    (internal : ¬ C.IsBoundaryVertex Set.univ (C.vertexOfCorner Set.univ p.1))
    {r : ℝ} (positive : 0 < r)
    (direction : Cap.horizontal (K.folding.germDirection p) =
      r • Cap.horizontal (K.folding.germDirection q)) :
    p = q ∨ p = C.mateGerm Set.univ q := by
  let vertex := C.vertexOfCorner Set.univ p.1
  let first : C.LinkGerm Set.univ vertex := ⟨p, rfl⟩
  have at_last : C.vertexOfCorner Set.univ q.1 = vertex :=
    K.projectedVertex_injective apex.symm
  let last : C.LinkGerm Set.univ vertex := ⟨q, at_last⟩
  by_cases same : 0 < K.projectedGermOrientation p * K.projectedGermOrientation q
  · exact Or.inl
      (K.projected_raw_germ_unique_of_same_orientation_positive_scale p q
        apex same positive direction)
  · have nonzero : K.projectedGermOrientation p * K.projectedGermOrientation q ≠ 0 :=
      mul_ne_zero (K.projectedGermOrientation_ne_zero _) (K.projectedGermOrientation_ne_zero _)
    have opposite : K.projectedGermOrientation p * K.projectedGermOrientation q < 0 :=
      lt_of_le_of_ne (le_of_not_gt same) nonzero
    have mate := K.projected_linkMate_orientation_product internal last
    have sign : 0 < K.projectedGermOrientation p *
        K.projectedGermOrientation (C.linkMate Set.univ vertex last).val := by
      rcases mul_neg_iff.mp opposite with ⟨ppos, qneg⟩ | ⟨pneg, qpos⟩
      · rcases mul_neg_iff.mp mate with ⟨mpos, _⟩ | ⟨_, qpos⟩
        · exact mul_pos ppos mpos
        · exact (qpos.not_gt qneg).elim
      · rcases mul_neg_iff.mp mate with ⟨_, qneg⟩ | ⟨mneg, _⟩
        · exact (qpos.not_gt qneg).elim
        · exact mul_pos_of_neg_of_neg pneg mneg
    have same_apex : (K.projectedTriangle p.1.1).vertex p.1.2 =
        (K.projectedTriangle (C.linkMate Set.univ vertex last).val.1.1).vertex
          (C.linkMate Set.univ vertex last).val.1.2 :=
      (K.projectedGerm_apex first).trans
        (K.projectedGerm_apex (C.linkMate Set.univ vertex last)).symm
    have same_direction : Cap.horizontal (K.folding.germDirection p) =
        r • Cap.horizontal (K.folding.germDirection (C.linkMate Set.univ vertex last).val) := by
      change _ = r • Cap.horizontal (K.folding.germDirection (C.mateGerm Set.univ q))
      rw [K.folding.germDirection_mate]
      exact direction
    exact Or.inr (K.projected_raw_germ_unique_of_same_orientation_positive_scale p _
      same_apex sign positive same_direction)

/-- The original full bank vectors agree exactly; no edge-length certificate is needed. -/
theorem projected_raw_direction_eq_of_positive_scale (p q : C.Germ)
    (apex : (K.projectedTriangle p.1.1).vertex p.1.2 =
      (K.projectedTriangle q.1.1).vertex q.1.2)
    (internal : ¬ C.IsBoundaryVertex Set.univ (C.vertexOfCorner Set.univ p.1))
    {r : ℝ} (positive : 0 < r)
    (direction : Cap.horizontal (K.folding.germDirection p) =
      r • Cap.horizontal (K.folding.germDirection q)) :
    K.folding.germDirection p = K.folding.germDirection q := by
  rcases K.projected_raw_germ_eq_or_mate_of_positive_scale p q apex internal positive direction with
    equal | equal
  · rw [equal]
  · rw [equal, K.folding.germDirection_mate]

end Unfoldings.ConvexCap
