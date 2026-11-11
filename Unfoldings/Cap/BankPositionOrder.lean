module

public import Unfoldings.Cap.BranchDisplacements
public import Unfoldings.Cap.ParentBankVectorOrder

/-!
# Actual branching bank position order

All descendants retain their sector label. In that one fixed quadrant frame,
their paired-vector differences point left and up. Summing the exact actual
contour displacement gives the same order for the two copies of the parent.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest.SectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C M.retain}
  (B : M.SectorFrameData positive small D)

/-- Fixed sector coordinates for actual developed position differences. -/
def sectorFrame (i : Fin 3) : Plane ≃ₗᵢ[ℝ] ℂ :=
  (M.calibratedFrame D B.anchor B.reference).trans
    (Complex.orthonormalBasisOneI.repr.trans (threeSectorFrame t positive small i).place)

theorem framedDirection_eq (i : Fin 3) (f : Face) (direction : Plane) :
    B.framedDirection i f direction = B.sectorFrame i (D.developedDirection K f direction) := rfl

include positive small in
theorem descendant_label {e v : C.Vertex Set.univ} (reaches : M.parents.Ancestor v e) :
    K.sourceSectorLabel t origin v = K.sourceSectorLabel t origin e := by
  obtain ⟨n, same⟩ := reaches
  have preserved := M.iterate_label positive.le small v n
  rw [same] at preserved
  exact preserved.symm

/-- Every descendant's actual paired-vector difference points weakly left and up. -/
theorem descendant_vector_gap_order
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    {e v : {v : C.Vertex Set.univ // v ∉ M.parents.roots}}
    (reaches : M.parents.Ancestor v.val e.val) :
    (B.sectorFrame (K.sourceSectorLabel t origin e.val)
      (M.parentExitVector D v - M.parentEntryVector D v)).re ≤ 0 ∧
    0 ≤ (B.sectorFrame (K.sourceSectorLabel t origin e.val)
      (M.parentExitVector D v - M.parentEntryVector D v)).im := by
  have ordered := B.parent_vector_order (M.parentBankOpening D v) budget
  rw [descendant_label (positive := positive) (small := small) reaches] at ordered
  simpa only [framedDirection_eq, map_sub, Complex.sub_re, Complex.sub_im,
    sub_nonpos, sub_nonneg, parentExitVector, parentEntryVector] using ordered

/-- The actual two parent copies have the same coordinate order, including every branch. -/
theorem parent_position_gap_order (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots})
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi) :
    (B.sectorFrame (K.sourceSectorLabel t origin e.val) (M.parentPositionGap D e)).re ≤ 0 ∧
    0 ≤ (B.sectorFrame (K.sourceSectorLabel t origin e.val) (M.parentPositionGap D e)).im := by
  classical
  rw [M.parent_position_gap_eq_descendant_sum D e, map_sum]
  simp only [Complex.re_sum, Complex.im_sum]
  constructor
  · apply Finset.sum_nonpos
    intro v _
    split_ifs with reaches
    · exact (B.descendant_vector_gap_order budget reaches).1
    · simp only [map_zero, Complex.zero_re, le_refl]
  · apply Finset.sum_nonneg
    intro v _
    split_ifs with reaches
    · exact (B.descendant_vector_gap_order budget reaches).2
    · simp only [map_zero, Complex.zero_im, le_refl]

end Unfoldings.ConvexCap.SectorForest.SectorFrameData
