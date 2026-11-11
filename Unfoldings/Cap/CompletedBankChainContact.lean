module

public import Unfoldings.Cap.CompletedBankChainOrder
public import Unfoldings.Cap.CompletedParentBankNoncrossing

/-! Interior contact of opposite whole branching banks is matched and flat. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)

include B in
/-- Regular points on different edges of the complete paired banks cannot meet. A contact on
one edge has the same physical parameter and zero whole-subtree curvature. All sibling
displacements are included through the actual branch-jump theorem. -/
theorem chain_interior_contact_flat {n : ℕ} (i : FiveSector)
    (chain : Fin n → {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (parents : ∀ j k : Fin n, k.val = j.val + 1 →
      N.spanningCompletion.parents.parent (chain j).val = (chain k).val)
    (sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (chain j))
    (directions : ∀ j, K.projectedVertex (N.spanningCompletion.parents.parent (chain j).val) -
      K.projectedVertex (chain j).val ∈ closedFiveSector t i)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (j k : Fin n) (s r : unitInterval)
    (s_positive : 0 < (s : ℝ)) (s_last : (s : ℝ) < 1)
    (r_positive : 0 < (r : ℝ)) (r_last : (r : ℝ) < 1)
    (same : N.parentExitPoint D (chain j) (1 - (s : ℝ)) =
      N.parentEntrancePoint D (chain k) (1 - (r : ℝ))) :
    j = k ∧ s = r ∧ N.completedSubtreeCurvature (chain j).val = 0 := by
  have strict_entry (a : Fin n) : StrictMono (fun u : unitInterval =>
      (B.sectorFrame i (N.parentEntrancePoint D (chain a) (1 - (u : ℝ)))).re) := by
    intro u v ordered
    have quadrant := (B.parent_vectors_quadrant i (chain a) (directions a)).1.1
    have product := mul_pos (sub_pos.mpr (show (u : ℝ) < v from ordered)) quadrant
    simp only [parentEntrancePoint, map_sub, map_smul, Complex.sub_re, Complex.smul_re,
      smul_eq_mul]
    linarith
  have strict_exit (a : Fin n) : StrictMono (fun u : unitInterval =>
      (B.sectorFrame i (N.parentExitPoint D (chain a) (1 - (u : ℝ)))).im) := by
    intro u v ordered
    have quadrant := (B.parent_vectors_quadrant i (chain a) (directions a)).2.2
    have product := mul_pos (sub_pos.mpr (show (u : ℝ) < v from ordered)) quadrant
    simp only [parentExitPoint, map_sub, map_smul, Complex.sub_im, Complex.smul_im,
      smul_eq_mul]
    linarith
  have indexes : j = k := by
    rcases lt_trichotomy j k with before | equal | after
    · have matched := (B.matched_bank_points_order i (chain j) (sectors j) (1 - (s : ℝ))
        (by linarith [s.property.1]) budget.le).1
      have strict := strict_entry j (show s < 1 from s_last)
      have later := B.chain_entrance_horizontal_order i chain parents sectors directions budget.le
        j k 1 r (Or.inl before)
      have gap := matched.trans_lt (strict.trans_le later)
      rw [same] at gap
      exact (lt_irrefl _ gap).elim
    · exact equal
    · have matched := (B.matched_bank_points_order i (chain k) (sectors k) (1 - (r : ℝ))
        (by linarith [r.property.1]) budget.le).2
      have strict := strict_exit k (show r < 1 from r_last)
      have later := B.chain_exit_vertical_order i chain parents sectors directions budget.le
        k j 1 s (Or.inl after)
      have gap := matched.trans_lt (strict.trans_le later)
      rw [same] at gap
      exact (lt_irrefl _ gap).elim
  subst k
  have parameters := B.bank_intersection_parameter_eq i (chain j) (directions j) (sectors j)
    (show 1 - (r : ℝ) ≤ 1 by linarith [r.property.1])
    (show 1 - (s : ℝ) ≤ 1 by linarith [s.property.1]) budget.le same.symm
  have matched : s = r := Subtype.ext (by linarith)
  refine ⟨rfl, matched, ?_⟩
  exact B.parent_bank_contact_flat i (chain j) (directions j) (sectors j)
    (show 1 - (r : ℝ) < 1 by linarith) (show 1 - (s : ℝ) < 1 by linarith) budget same.symm

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
