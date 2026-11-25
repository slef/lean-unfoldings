module

public import Unfoldings.Roof.FlatRestrictedCorner
public import Unfoldings.Roof.GraphLensCornerFan
public import Unfoldings.Roof.ClosingGraphTwoLinks

/-! The actual upper fan at the connector bend has the one-support-plane angle error. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Filter Topology InnerProductGeometry PlanarTopology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

private theorem abs_sectionAngleError_of_two_rays (f : Face) {x y u v : Plane}
    (u_ne : u ≠ 0) (v_ne : v ≠ 0) (different : angle x y ≠ 0)
    (on_first : (∃ t : ℝ, 0 < t ∧ x = t • u) ∨ ∃ t : ℝ, 0 < t ∧ x = t • v)
    (on_last : (∃ t : ℝ, 0 < t ∧ y = t • u) ∨ ∃ t : ℝ, 0 < t ∧ y = t • v) :
    |angle (K.sectionDirection f x) (K.sectionDirection f y) - angle x y| =
      |angle (K.sectionDirection f u) (K.sectionDirection f v) - angle u v| := by
  rcases on_first with ⟨s, sp, rfl⟩ | ⟨s, sp, rfl⟩ <;>
    rcases on_last with ⟨t, tp, rfl⟩ | ⟨t, tp, rfl⟩
  · exact (different (by rw [angle_smul_left_of_pos _ _ sp,
      angle_smul_right_of_pos _ _ tp, angle_self u_ne])).elim
  · rw [K.sectionDirection_smul, K.sectionDirection_smul]
    simp only [angle_smul_left_of_pos _ _ sp, angle_smul_right_of_pos _ _ tp]
  · rw [K.sectionDirection_smul, K.sectionDirection_smul]
    simp only [angle_smul_left_of_pos _ _ sp, angle_smul_right_of_pos _ _ tp,
      angle_comm v u, angle_comm (K.sectionDirection f v) (K.sectionDirection f u)]
  · exact (different (by rw [angle_smul_left_of_pos _ _ sp,
      angle_smul_right_of_pos _ _ tp, angle_self v_ne])).elim

open Classical in
set_option maxHeartbeats 1200000 in
/-- At an interior graph bend in an old support plane, the absolute regional
excess is exactly the angle error of the incoming and outgoing links. -/
theorem abs_graphClosingBend_excess_eq {g : ℝ → ℝ} (hg : Continuous g) {a c b : Plane}
    (first_progress : a 0 < c 0) (last_progress : c 0 < b 0)
    (trace : graphPoint g '' Set.Icc (a 0) (b 0) = segment ℝ a c ∪ segment ℝ c b)
    (sample : Face → Plane) (sample_in : ∀ i, sample i ∈ interior (K.projectedTriangle i).carrier)
    (endpoints : ∀ i z, z ∈ interior (K.projectedTriangle i).carrier → z 0 ≠ a 0 ∧ z 0 ≠ b 0)
    (aligned : ∀ i, Disjoint (interior (K.projectedTriangle i).carrier)
      (graphPoint g '' Set.Icc (a 0) (b 0)))
    (w : C.Vertex Set.univ) (marked : K.projectedVertex w = c) (inside : c ∈ interior K.footprint)
    (f : Face) (slopes : ∀ j i, C.vertexOfCorner Set.univ (j, i) = w →
      K.normalSlope j = K.normalSlope f) :
    |K.regionalAngleExcess (facesAboveGraph sample g (a 0) (b 0)) w| =
      |angle (K.sectionDirection f (c - a)) (K.sectionDirection f (b - c)) -
        angle (c - a) (b - c)| := by
  let U := facesAboveGraph sample g (a 0) (b 0)
  let R := C.restrictFaces U
  let F := K.folding.restrictFaces U
  let d := c - a
  let e := b - c
  have d_ne : d ≠ 0 := sub_ne_zero.mpr (fun h =>
    first_progress.ne (congrArg (fun z : Plane => z 0) h.symm))
  have e_ne : e ≠ 0 := sub_ne_zero.mpr (fun h =>
    last_progress.ne (congrArg (fun z : Plane => z 0) h.symm))
  have c_graph : c ∈ graphPoint g '' Set.Icc (a 0) (b 0) := trace.symm.subset
    (Or.inl (right_mem_segment ℝ a c))
  have equation : c 1 = g (c 0) := by
    obtain ⟨t, _, rfl⟩ := c_graph
    rfl
  have w_inside : K.projectedVertex w ∈ interior K.footprint := marked.symm ▸ inside
  obtain ⟨p, original, position, turn⟩ := K.exists_boundaryEnd_facesAboveGraph hg sample sample_in
    endpoints aligned w w_inside (marked.symm ▸ ⟨first_progress, last_progress⟩) (marked.symm ▸ equation)
  let q := R.boundaryMate Set.univ p
  have local_rays : ∀ᶠ z in 𝓝 c, z ∈ frontier (K.restrictedCarrier U) →
      z - c ∈ nonnegativeRay (-d) ∪ nonnegativeRay e := by
    have open_window : IsOpen ({z : Plane | z 0 ∈ Set.Ioo (a 0) (b 0)}) :=
      isOpen_Ioo.preimage (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).continuous
    filter_upwards [isOpen_interior.mem_nhds inside,
      open_window.mem_nhds ⟨first_progress, last_progress⟩] with z in_roof window boundary
    have on_graph := K.eq_graph_of_mem_frontier_facesAboveGraph hg sample sample_in endpoints
      aligned in_roof window boundary
    have on_trace : z ∈ graphPoint g '' Set.Icc (a 0) (b 0) := by
      refine ⟨z 0, Set.Ioo_subset_Icc_self window, ?_⟩
      apply PiLp.ext
      intro i
      fin_cases i
      · rfl
      · exact on_graph.symm
    rcases trace.subset on_trace with left | right
    · left
      obtain ⟨t, parameter, rfl⟩ := (segment_eq_image_lineMap ℝ c a).subset
        (by simpa only [segment_symm ℝ c a] using left)
      refine ⟨t, parameter.1, ?_⟩
      rw [AffineMap.lineMap_apply_module', add_sub_cancel_right]
      simp only [d, neg_sub]
    · right
      obtain ⟨t, parameter, rfl⟩ := (segment_eq_image_lineMap ℝ c b).subset right
      exact ⟨t, parameter.1, by rw [AffineMap.lineMap_apply_module', add_sub_cancel_right]⟩
  have p_pos : Cap.horizontal (F.boundaryPosition p) = c := position.trans marked
  have q_pos : Cap.horizontal (F.boundaryPosition q) = c := by
    rw [F.boundaryPosition_mate p, p_pos]
  have inner_vertex := (K.projectedVertex_mem_interior_iff w).mp w_inside
  have exact_error := K.abs_flat_restrictedBoundaryTurnError_eq_angle U p
    (original.symm ▸ inner_vertex) f (fun j i at_p => slopes j i (at_p.trans original))
  dsimp only at exact_error
  rw [turn, abs_neg] at exact_error
  rw [exact_error]
  rw [K.abs_sectionAngleError_of_two_rays f (neg_ne_zero.mpr d_ne) e_ne
    (K.restricted_boundary_rays_angle_ne_zero U p)
    (K.restricted_bank_direction_of_local_two_rays U p (-d) e (by rwa [p_pos]))
    (K.restricted_bank_direction_of_local_two_rays U q (-d) e (by rwa [q_pos]))]
  rw [K.sectionDirection_neg, angle_neg_left, angle_neg_left, sub_sub_sub_cancel_left, abs_sub_comm]

end Unfoldings.ConvexRoof
