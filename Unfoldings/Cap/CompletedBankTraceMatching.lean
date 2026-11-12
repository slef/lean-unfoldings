module

public import Unfoldings.Cap.CompletedBankGraphSides
public import Unfoldings.Cap.TraceFacingFace

/-! One-sided strip traces select the actual named parent banks, with all side signs derived. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)
  {t : ℝ} (positive : 0 < t) (small : t < 1) (i : FiveSector)
  (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
  (direction : K.projectedVertex (N.spanningCompletion.parents.parent e.val) -
    K.projectedVertex e.val ∈ closedFiveSector t i)

theorem parentCutGraph_local_cut_interval (on_cut : K.projectedVertex e.val ∈ cuts)
    (S : MonotoneStrip) (cutoff : ℝ)
    (avoids : ∀ z ∈ S.strictCarrier, z.re + z.im ∈ Set.Icc 0 cutoff →
      source + (fiveSectorFrame t positive small i).place.symm z ∉ cuts)
    {z : ℂ}
    (member : source + (fiveSectorFrame t positive small i).place.symm z ∈
      segment ℝ (K.projectedVertex e.val)
        (K.projectedVertex (N.spanningCompletion.parents.parent e.val)))
    (regular : ∀ f j, source + (fiveSectorFrame t positive small i).place.symm z ≠
      (K.projectedTriangle f).vertex j)
    (slab : z.re + z.im ∈ Set.Ioo 0 cutoff) :
    let H := N.parentCutGraph positive small i e direction
    H.coordinate (z.re + z.im) = z.re ∧
      ∃ a b, z.re + z.im ∈ Set.Ioo a b ∧
        ∀ h ∈ Set.Ioo a b, H.point h ∉ S.strictCarrier := by
  let frame := (fiveSectorFrame t positive small i).place
  let p := source + frame.symm z
  have input : frame (p - source) = z := by
    have vector : p - source = frame.symm z := by dsimp only [p]; abel
    rw [vector, frame.apply_symm_apply]
  have not_vertex (v : C.Vertex Set.univ) : p ≠ K.projectedVertex v := by
    obtain ⟨⟨f, j⟩, rfl⟩ := C.vertexOfCorner_surjective Set.univ v
    exact regular f j
  have touch := N.parentCutGraph_coordinate_of_mem_segment positive small i e direction member
  have interval := N.parentCutGraph_strict_height positive small i e direction member
    (not_vertex e.val) (not_vertex (N.spanningCompletion.parents.parent e.val))
  dsimp only [frame, p] at input
  dsimp only at touch interval
  rw [input] at touch interval
  let first := (frame (K.projectedVertex e.val - source)).re +
    (frame (K.projectedVertex e.val - source)).im
  let last := (frame (K.projectedVertex (N.spanningCompletion.parents.parent e.val) - source)).re +
    (frame (K.projectedVertex (N.spanningCompletion.parents.parent e.val) - source)).im
  let a := max first 0
  let b := min last cutoff
  have near : z.re + z.im ∈ Set.Ioo a b :=
    ⟨max_lt_iff.mpr ⟨interval.1, slab.1⟩, lt_min_iff.mpr ⟨interval.2, slab.2⟩⟩
  refine ⟨touch, a, b, near, fun h within => ?_⟩
  apply N.parentCutGraph_avoids_strict_strip positive small i e direction on_cut S cutoff avoids
  · exact ⟨(le_max_left first 0).trans within.1.le,
      within.2.le.trans (min_le_left last cutoff)⟩
  · exact ⟨(le_max_right first 0).trans within.1.le,
      within.2.le.trans (min_le_right last cutoff)⟩

include direction in
/-- The lower-wall trace uses the actual entrance chart. Local side signs, seam labels,
and cut-graph avoidance are derived from the named bank and physical forest. -/
theorem trace_lower_parent_cut_eq_entrance (D : FacewiseDevelopment C N.completedRetain)
    (calibration : Plane ≃ₗᵢ[ℝ] ℂ) {G : ℂ → ℂ} {domain : Set ℂ} {z : ℂ}
    (trace : D.TraceVisibleAt K source calibration (fiveSectorFrame t positive small i).place
      G domain z)
    (S : MonotoneStrip) (cutoff : ℝ) (strict : domain ⊆ S.strictCarrier)
    (on_cut : K.projectedVertex e.val ∈ cuts)
    (avoids : ∀ x ∈ S.strictCarrier, x.re + x.im ∈ Set.Icc 0 cutoff →
      source + (fiveSectorFrame t positive small i).place.symm x ∉ cuts)
    (member : source + (fiveSectorFrame t positive small i).place.symm z ∈
      segment ℝ (K.projectedVertex e.val)
        (K.projectedVertex (N.spanningCompletion.parents.parent e.val)))
    (regular : ∀ f j, source + (fiveSectorFrame t positive small i).place.symm z ≠
      (K.projectedTriangle f).vertex j)
    (slab : z.re + z.im ∈ Set.Ioo 0 cutoff)
    (on_wall : S.lower.coordinate (z.re + z.im) = z.re)
    (width : S.lower.coordinate (z.re + z.im) < S.upper.coordinate (z.re + z.im)) :
    G z = D.centeredCoordinatePlacement K source calibration
      (fiveSectorFrame t positive small i).place (N.parentBankOpening D e).entranceFace z := by
  let frame := (fiveSectorFrame t positive small i).place
  let H := N.parentCutGraph positive small i e direction
  obtain ⟨touch, a, b, near, local_avoid⟩ := N.parentCutGraph_local_cut_interval positive small
    i e direction on_cut S cutoff avoids member regular slab
  obtain ⟨c, d, around, _, side⟩ := S.cut_below_lower_locally H near
    (touch.trans on_wall.symm) width local_avoid
  let U := {x : ℂ | x.re + x.im ∈ Set.Ioo c d}
  have opened : IsOpen U := isOpen_Ioo.preimage
    (Complex.continuous_re.add Complex.continuous_im)
  apply D.traceVisibleAt_eq_of_local_side K source calibration frame trace
    (N.parentBankOpening D e).entranceFace (N.parentBankOpening D e).exitFace
    (N.parent_bank_faces_of_regular e D member regular)
    (fun x => x.re - H.coordinate (x.re + x.im)) U opened around
  · intro x in_U
    exact sub_pos.mpr ((side _ in_U.2).trans_lt (strict in_U.1).1)
  · intro x in_face
    exact sub_nonpos.mpr (N.parentCutGraph_exit_side positive small i e direction D in_face)

include direction in
theorem trace_upper_parent_cut_eq_exit (D : FacewiseDevelopment C N.completedRetain)
    (calibration : Plane ≃ₗᵢ[ℝ] ℂ) {G : ℂ → ℂ} {domain : Set ℂ} {z : ℂ}
    (trace : D.TraceVisibleAt K source calibration (fiveSectorFrame t positive small i).place
      G domain z)
    (S : MonotoneStrip) (cutoff : ℝ) (strict : domain ⊆ S.strictCarrier)
    (on_cut : K.projectedVertex e.val ∈ cuts)
    (avoids : ∀ x ∈ S.strictCarrier, x.re + x.im ∈ Set.Icc 0 cutoff →
      source + (fiveSectorFrame t positive small i).place.symm x ∉ cuts)
    (member : source + (fiveSectorFrame t positive small i).place.symm z ∈
      segment ℝ (K.projectedVertex e.val)
        (K.projectedVertex (N.spanningCompletion.parents.parent e.val)))
    (regular : ∀ f j, source + (fiveSectorFrame t positive small i).place.symm z ≠
      (K.projectedTriangle f).vertex j)
    (slab : z.re + z.im ∈ Set.Ioo 0 cutoff)
    (on_wall : S.upper.coordinate (z.re + z.im) = z.re)
    (width : S.lower.coordinate (z.re + z.im) < S.upper.coordinate (z.re + z.im)) :
    G z = D.centeredCoordinatePlacement K source calibration
      (fiveSectorFrame t positive small i).place (N.parentBankOpening D e).exitFace z := by
  let frame := (fiveSectorFrame t positive small i).place
  let H := N.parentCutGraph positive small i e direction
  obtain ⟨touch, a, b, near, local_avoid⟩ := N.parentCutGraph_local_cut_interval positive small
    i e direction on_cut S cutoff avoids member regular slab
  obtain ⟨c, d, around, _, side⟩ := S.cut_above_upper_locally H near
    (touch.trans on_wall.symm) width local_avoid
  let U := {x : ℂ | x.re + x.im ∈ Set.Ioo c d}
  have opened : IsOpen U := isOpen_Ioo.preimage
    (Complex.continuous_re.add Complex.continuous_im)
  apply D.traceVisibleAt_eq_of_local_side K source calibration frame trace
    (N.parentBankOpening D e).exitFace (N.parentBankOpening D e).entranceFace
    (fun f in_face => (N.parent_bank_faces_of_regular e D member regular f in_face).symm)
    (fun x => H.coordinate (x.re + x.im) - x.re) U opened around
  · intro x in_U
    exact sub_pos.mpr ((strict in_U.1).2.trans_le (side _ in_U.2))
  · intro x in_face
    exact sub_nonpos.mpr (N.parentCutGraph_entrance_side positive small i e direction D in_face)

end Unfoldings.ConvexCap.RadialCutForest
