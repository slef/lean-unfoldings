module

public import Unfoldings.Basic
public import Unfoldings.Geometry.HeightNetworkLocalGraph
public import Unfoldings.Geometry.MonotoneStripSubdivision

/-! Exact affine cut graphs and strip avoidance in arbitrary centered orthogonal frames. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem linear_segment_strict_bounds {E : Type*} [AddCommGroup E] [Module ℝ E]
    (height : E →ₗ[ℝ] ℝ) {a b x : E} (ordered : height a < height b)
    (member : x ∈ segment ℝ a b) (first : x ≠ a) (last : x ≠ b) :
    height x ∈ Set.Ioo (height a) (height b) := by
  have bounds := linear_segment_bounds height ordered.le member
  have left : height a ≠ height x := by
    intro equal
    exact first (point_eq_of_mem_segment_of_linear_eq height ordered member
      (left_mem_segment ℝ a b) equal.symm)
  have right : height x ≠ height b := by
    intro equal
    exact last (point_eq_of_mem_segment_of_linear_eq height ordered member
      (right_mem_segment ℝ a b) equal)
  exact ⟨lt_of_le_of_ne bounds.1 left, lt_of_le_of_ne bounds.2 right⟩

namespace MonotoneHeightGraph

theorem through_point_mem_segment (p q : ℂ) (horizontal : p.re ≤ q.re)
    (vertical : p.im ≤ q.im) (genuine : 0 < q.re + q.im - (p.re + p.im))
    {h : ℝ} (inside : h ∈ Set.Icc (p.re + p.im) (q.re + q.im)) :
    (through p q horizontal vertical genuine).point h ∈ segment ℝ p q := by
  let L := complexDiagonalHeight
  have ordered : L p ≤ L q := (sub_pos.mp genuine).le
  have height : h ∈ segment ℝ (L p) (L q) := by
    rw [segment_eq_Icc ordered]
    exact inside
  have image : L '' segment ℝ p q = segment ℝ (L p) (L q) :=
    image_segment ℝ L.toAffineMap p q
  rw [← image] at height
  obtain ⟨z, member, equal⟩ := height
  have coordinate := through_coordinate_of_mem_segment p q horizontal vertical genuine member
  have point := (through p q horizontal vertical genuine).point_eq_of_coordinate z coordinate
  change z.re + z.im = h at equal
  rw [equal] at point
  exact point.symm ▸ member

theorem through_side_identity (p q : ℂ) (horizontal : p.re ≤ q.re)
    (vertical : p.im ≤ q.im) (genuine : 0 < q.re + q.im - (p.re + p.im)) (z : ℂ) :
    (q.re + q.im - (p.re + p.im)) *
      ((through p q horizontal vertical genuine).coordinate (z.re + z.im) - z.re) =
      (starRingEnd ℂ (q - p) * (z - p)).im := by
  dsimp only [through, affine]
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im]
  field_simp [genuine.ne']
  ring

theorem through_side_nonneg_iff (p q : ℂ) (horizontal : p.re ≤ q.re)
    (vertical : p.im ≤ q.im) (genuine : 0 < q.re + q.im - (p.re + p.im)) (z : ℂ) :
    z.re ≤ (through p q horizontal vertical genuine).coordinate (z.re + z.im) ↔
      0 ≤ (starRingEnd ℂ (q - p) * (z - p)).im := by
  rw [← through_side_identity p q horizontal vertical genuine z,
    mul_nonneg_iff_of_pos_left genuine, sub_nonneg]

theorem through_side_nonpos_iff (p q : ℂ) (horizontal : p.re ≤ q.re)
    (vertical : p.im ≤ q.im) (genuine : 0 < q.re + q.im - (p.re + p.im)) (z : ℂ) :
    (through p q horizontal vertical genuine).coordinate (z.re + z.im) ≤ z.re ↔
      (starRingEnd ℂ (q - p) * (z - p)).im ≤ 0 := by
  rw [← through_side_identity p q horizontal vertical genuine z]
  constructor
  · intro bound
    exact mul_nonpos_of_nonneg_of_nonpos genuine.le (sub_nonpos.mpr bound)
  · intro bound
    by_contra reversed
    exact not_lt_of_ge bound (mul_pos genuine (sub_pos.mpr (lt_of_not_ge reversed)))

end MonotoneHeightGraph

theorem framed_cut_segment_avoids_strict_strip (q : Plane) (frame : Plane ≃ₗᵢ[ℝ] ℂ)
    (cuts : Set Plane) (a b : Plane) (cut : segment ℝ a b ⊆ cuts)
    (S : MonotoneStrip) (cutoff : ℝ)
    (avoids : ∀ z ∈ S.strictCarrier, z.re + z.im ∈ Set.Icc 0 cutoff →
      q + frame.symm z ∉ cuts)
    (horizontal : (frame (a - q)).re ≤ (frame (b - q)).re)
    (vertical : (frame (a - q)).im ≤ (frame (b - q)).im)
    (genuine : 0 < ((frame (b - q)).re + (frame (b - q)).im) -
      ((frame (a - q)).re + (frame (a - q)).im))
    {h : ℝ}
    (inside : h ∈ Set.Icc ((frame (a - q)).re + (frame (a - q)).im)
      ((frame (b - q)).re + (frame (b - q)).im))
    (slab : h ∈ Set.Icc 0 cutoff) :
    (MonotoneHeightGraph.through (frame (a - q)) (frame (b - q))
      horizontal vertical genuine).point h ∉ S.strictCarrier := by
  let H := MonotoneHeightGraph.through (frame (a - q)) (frame (b - q))
    horizontal vertical genuine
  let A := frame.symm.toAffineIsometryEquiv.toAffineEquiv.trans (AffineEquiv.constVAdd ℝ Plane q)
  have first : A (frame (a - q)) = a := by
    change q + frame.symm (frame (a - q)) = a
    rw [frame.symm_apply_apply]
    abel
  have last : A (frame (b - q)) = b := by
    change q + frame.symm (frame (b - q)) = b
    rw [frame.symm_apply_apply]
    abel
  have on_segment := MonotoneHeightGraph.through_point_mem_segment (frame (a - q))
    (frame (b - q)) horizontal vertical genuine inside
  have physical : A (H.point h) ∈ segment ℝ a b := by
    have image : A '' segment ℝ (frame (a - q)) (frame (b - q)) =
        segment ℝ (A (frame (a - q))) (A (frame (b - q))) :=
      image_segment ℝ A.toAffineMap _ _
    rw [first, last] at image
    exact image.subset ⟨H.point h, on_segment, rfl⟩
  intro strict
  have height : (H.point h).re + (H.point h).im ∈ Set.Icc 0 cutoff := by
    rw [H.point_height]
    exact slab
  exact avoids (H.point h) strict height (cut physical)

end Unfoldings
