module

public import Unfoldings.Roof.VertexContourExcursion
public import Unfoldings.Roof.CurvaturePrunedForest

/-! A zero displacement excursion contains only flat selected subtrees. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest.SectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C M.retain}
  (B : M.SectorFrameData positive small D)

include B in
/-- Within one descendant region, an excursion closes exactly when each opening it
contains has zero total curvature. No assumption is made about curvature at its endpoints. -/
theorem vertex_excursion_gap_eq_zero_iff_selected_subtrees_flat
    {e : C.Vertex Set.univ}
    (E : M.VertexContourExcursion e)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi) :
    D.boundaryPosition (M.projectionContour.cycle.point
      (finRotate (M.projectionContour.length + 1) E.last)) =
        D.boundaryPosition (M.projectionContour.cycle.point
          (finRotate (M.projectionContour.length + 1) E.first)) ↔
      ∀ v : {w : C.Vertex Set.univ // w ∉ M.parents.roots},
        E.region (M.parentBankOpening D v).enter → M.subtreeCurvature v.val = 0 := by
  classical
  let frame := B.sectorFrame (K.sourceSectorLabel t origin e)
  let term := fun v : {w : C.Vertex Set.univ // w ∉ M.parents.roots} =>
    if E.region (M.parentBankOpening D v).enter then
      (frame (M.parentExitVector D v - M.parentEntryVector D v)).re else 0
  have nonpositive (v : {w : C.Vertex Set.univ // w ∉ M.parents.roots}) : term v ≤ 0 := by
    dsimp only [term]
    split_ifs with selected
    · have ordered := B.parent_vector_order (M.parentBankOpening D v) budget.le
      rw [descendant_label (positive := positive) (small := small)
        (E.selected_descendant D v selected)] at ordered
      have gap : (frame (M.parentExitVector D v - M.parentEntryVector D v)).re ≤ 0 ∧
          0 ≤ (frame (M.parentExitVector D v - M.parentEntryVector D v)).im := by
        simpa only [frame, framedDirection_eq, map_sub, Complex.sub_re, Complex.sub_im,
          sub_nonpos, sub_nonneg, parentExitVector, parentEntryVector] using ordered
      exact gap.1
    · exact le_rfl
  constructor
  · intro same
    have gap := E.displacement D
    rw [same, sub_self] at gap
    have zero : ∑ v, term v = 0 := by
      have coordinate := congrArg (fun z => (frame z).re) gap
      simpa only [term, map_sum, Complex.re_sum, apply_ite, map_zero, Complex.zero_re]
        using coordinate.symm
    have each := (Finset.sum_eq_zero_iff_of_nonpos (fun v _ => nonpositive v)).mp zero
    intro v selected
    have zero_gap : (frame (M.parentExitVector D v - M.parentEntryVector D v)).re = 0 := by
      simpa only [term, selected, ite_true] using each v (Finset.mem_univ v)
    by_contra nonflat
    have curved : 0 < M.subtreeCurvature v.val :=
      lt_of_le_of_ne (M.subtreeCurvature_nonneg v.val) (Ne.symm nonflat)
    have strict := (B.parent_vector_strict_order v budget curved).1
    rw [descendant_label (positive := positive) (small := small)
      (E.selected_descendant D v selected)] at strict
    exact strict.ne zero_gap
  · intro flat
    apply sub_eq_zero.mp
    rw [E.displacement D]
    apply Finset.sum_eq_zero
    intro v _
    split_ifs with selected
    · rw [M.parent_vectors_eq_of_flat D v (flat v selected), sub_self]
    · rfl

end Unfoldings.ConvexRoof.SectorForest.SectorFrameData
