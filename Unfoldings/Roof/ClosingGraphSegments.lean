module

public import Unfoldings.Roof.AboveGraphClosingLink
public import Unfoldings.Geometry.TwoLinkMonotoneChain

/-! Enumerate the actual fine vertices on an open straight segment of an aligned graph. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Filter Topology PlanarTopology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f)
  (sample : Face → Plane) (sample_in : ∀ i, sample i ∈ interior (K.projectedTriangle i).carrier)
  (endpoints : ∀ i z, z ∈ interior (K.projectedTriangle i).carrier → z 0 ≠ a ∧ z 0 ≠ b)
  (aligned : ∀ i, Disjoint (interior (K.projectedTriangle i).carrier) (graphPoint f '' Set.Icc a b))
  (in_roof : graphPoint f '' Set.Icc a b ⊆ interior K.footprint)

local notation "Above" => facesAboveGraph sample f a b

private theorem graphPoint_mem {x : Plane} (window : x 0 ∈ Set.Icc a b) (equation : x 1 = f (x 0)) :
    x ∈ graphPoint f '' Set.Icc a b := by
  refine ⟨x 0, window, ?_⟩
  ext i
  fin_cases i
  · rfl
  · exact equation.symm

include hf sample_in endpoints aligned in_roof in
set_option maxHeartbeats 1300000 in
open Classical in
/-- On an open link, collect all fine contacts exactly once. The second
piece of the closing graph stays out of each contact neighborhood. -/
theorem exists_regularClosingLink_on_graphSegment {p q : Plane}
    (advance : p 0 < q 0) (start : a ≤ p 0) (finish : q 0 ≤ b)
    (in_graph : segment ℝ p q ⊆ graphPoint f '' Set.Icc a b)
    (remainder : Set Plane) (closed : IsClosed remainder)
    (cover : graphPoint f '' Set.Icc a b ⊆ segment ℝ p q ∪ remainder)
    (outside : Disjoint (openSegment ℝ p q) remainder)
    (regular : ∀ w : C.Vertex Set.univ, K.projectedVertex w ∈ openSegment ℝ p q →
      K.HasRegularSectionSlopes w (q - p)) :
    let I := {w : C.Vertex Set.univ // K.projectedVertex w ∈ openSegment ℝ p q}
    let direction := NormedSpace.normalize (q - p)
    ∃ L : K.RegularClosingLink Above p direction I,
      (∀ i, 0 < L.time i ∧ L.time i < ‖q - p‖) ∧
      ∀ i, K.restrictedBoundaryTurnError Above (L.bank i) = -K.regionalAngleExcess Above i.val := by
  let I := {w : C.Vertex Set.univ // K.projectedVertex w ∈ openSegment ℝ p q}
  let d := NormedSpace.normalize (q - p)
  let length := ‖q - p‖
  have different : q - p ≠ 0 := by
    intro zero
    exact advance.ne (congrArg (fun x : Plane => x 0) (sub_eq_zero.mp zero).symm)
  have length_pos : 0 < length := norm_pos_iff.mpr different
  have unit : ‖d‖ = 1 := NormedSpace.norm_normalize different
  have genuine : d ≠ 0 := by
    intro zero
    rw [zero, norm_zero] at unit
    norm_num at unit
  have line_form (t : ℝ) : AffineMap.lineMap p q t = p + (t * length) • d := by
    rw [AffineMap.lineMap_apply_module']
    change t • (q - p) + p = p + (t * ‖q - p‖) • NormedSpace.normalize (q - p)
    rw [mul_smul, NormedSpace.norm_smul_normalize, add_comm]
  have window_time (i : I) : ∃ t : ℝ, t ∈ Set.Ioo 0 1 ∧
      AffineMap.lineMap p q t = K.projectedVertex i.val := by
    exact (openSegment_eq_image_lineMap ℝ p q).subset i.property
  choose t parameter at_vertex using window_time
  let time (i : I) := t i * length
  have at_time (i : I) : K.projectedVertex i.val = p + time i • d :=
    (at_vertex i).symm.trans (line_form (t i))
  have graph (i : I) : K.projectedVertex i.val ∈ graphPoint f '' Set.Icc a b :=
    in_graph (openSegment_subset_segment ℝ p q i.property)
  have window (i : I) : K.projectedVertex i.val 0 ∈ Set.Ioo a b := by
    have at_x := congrArg (fun z : Plane => z 0) (at_vertex i)
    rw [AffineMap.lineMap_apply_module'] at at_x
    change t i * (q 0 - p 0) + p 0 = K.projectedVertex i.val 0 at at_x
    have left := mul_pos (parameter i).1 (sub_pos.mpr advance)
    have right := mul_pos (sub_pos.mpr (parameter i).2) (sub_pos.mpr advance)
    exact ⟨by linarith only [start, at_x, left], by linarith only [finish, at_x, right]⟩
  have on_graph (i : I) : K.projectedVertex i.val 1 = f (K.projectedVertex i.val 0) := by
    obtain ⟨s, _, equal⟩ := graph i
    rw [← equal]
    rfl
  have near_line (i : I) : ∀ᶠ z in 𝓝 (K.projectedVertex i.val),
      z 0 ∈ Set.Ioo a b → z 1 = f (z 0) → ∃ s : ℝ, z = p + s • d := by
    have absent : K.projectedVertex i.val ∉ remainder :=
      fun h => Set.disjoint_left.mp outside i.property h
    filter_upwards [closed.isOpen_compl.mem_nhds absent] with z off_rest
    intro in_window equation
    obtain ⟨s, _, position⟩ := (segment_eq_image_lineMap ℝ p q).subset
      ((cover (graphPoint_mem (Set.Ioo_subset_Icc_self in_window) equation)).resolve_right off_rest)
    exact ⟨s * length, position.symm.trans (line_form s)⟩
  have regular_normal (i : I) : K.HasRegularSectionSlopes i.val d := by
    obtain ⟨s, t, slopes, transverse⟩ := regular i.val i.property
    refine ⟨s, t, slopes, transverse.imp_right ?_⟩
    intro nonzero
    change inner ℝ (s - t) (‖q - p‖⁻¹ • (q - p)) ≠ 0
    rw [real_inner_smul_right]
    exact mul_ne_zero (inv_ne_zero length_pos.ne') nonzero
  obtain ⟨L, same, turns⟩ := K.exists_regularClosingLink_facesAboveGraph hf sample sample_in endpoints
    aligned p d genuine (Subtype.val : I → C.Vertex Set.univ) Subtype.val_injective
    time at_time (fun i => in_roof (graph i)) window on_graph near_line regular_normal
  refine ⟨L, fun i => ?_, turns⟩
  change 0 < L.time i ∧ L.time i < length
  rw [same]
  exact ⟨mul_pos (parameter i).1 length_pos,
    (mul_lt_mul_of_pos_right (parameter i).2 length_pos).trans_eq (one_mul length)⟩

end Unfoldings.ConvexRoof
