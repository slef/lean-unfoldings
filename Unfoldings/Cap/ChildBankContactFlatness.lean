module

public import Unfoldings.Cap.CurvaturePrunedForest

/-! Coincident child endpoints of actual parent banks force every proper descendant subtree flat. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest.SectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C M.retain}
  (B : M.SectorFrameData positive small D)

include B in
/-- At a branch vertex, a closed endpoint contact is possible precisely when every
proper descendant opening is flat. The curvature at the endpoint itself is unrestricted. -/
theorem child_bank_points_eq_iff_flat_proper_descendants
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots})
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi) :
    M.parentEntrancePoint D e 1 = M.parentExitPoint D e 1 ↔
      ∀ v : C.Vertex Set.univ, M.parents.Ancestor v e.val → v ≠ e.val →
        M.subtreeCurvature v = 0 := by
  classical
  let frame := B.sectorFrame (K.sourceSectorLabel t origin e.val)
  let term := fun v : {v : C.Vertex Set.univ // v ∉ M.parents.roots} =>
    if M.parents.Ancestor v.val e.val then
      (frame (M.parentExitVector D v - M.parentEntryVector D v)).re else 0
  have nonpositive (v : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) : term v ≤ 0 := by
    dsimp only [term]
    split_ifs with reaches
    · exact (B.descendant_vector_gap_order budget.le reaches).1
    · exact le_rfl
  constructor
  · intro same
    have gap := M.matched_bank_gap_eq D e 1
    rw [same, sub_self, sub_self, zero_smul, add_zero] at gap
    have zero : ∑ v ∈ Finset.univ.erase e, term v = 0 := by
      have coordinate := congrArg (fun z => (frame z).re) gap
      simpa only [term, map_sum, Complex.re_sum, apply_ite, map_zero, Complex.zero_re]
        using coordinate.symm
    have each := (Finset.sum_eq_zero_iff_of_nonpos (fun v _ => nonpositive v)).mp zero
    intro v reaches different
    let a : {v : C.Vertex Set.univ // v ∉ M.parents.roots} :=
      ⟨v, M.parents.descendant_nonroot e.property reaches⟩
    have a_different : a ≠ e := fun equal => different (congrArg Subtype.val equal)
    have zero_a := each a (Finset.mem_erase.mpr ⟨a_different, Finset.mem_univ a⟩)
    have zero_gap : (frame (M.parentExitVector D a - M.parentEntryVector D a)).re = 0 := by
      simpa only [term, a, reaches, ite_true] using zero_a
    by_contra nonflat
    have curved : 0 < M.subtreeCurvature a.val :=
      lt_of_le_of_ne (M.subtreeCurvature_nonneg v) (Ne.symm nonflat)
    have strict := (B.parent_vector_strict_order a budget curved).1
    rw [descendant_label (positive := positive) (small := small) reaches] at strict
    exact strict.ne zero_gap
  · intro flat
    apply Eq.symm
    apply sub_eq_zero.mp
    rw [M.matched_bank_gap_eq D e 1, sub_self, zero_smul, add_zero]
    apply Finset.sum_eq_zero
    intro v member
    split_ifs with reaches
    · have different : v.val ≠ e.val := fun equal =>
        (Finset.mem_erase.mp member).1 (Subtype.ext equal)
      rw [M.parent_vectors_eq_of_flat D v (flat v.val reaches different), sub_self]
    · rfl

end Unfoldings.ConvexCap.SectorForest.SectorFrameData
