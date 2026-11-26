module

public import Unfoldings.Roof.ClosingGraphTurnBudget
public import Unfoldings.Roof.CompleteClosingTrace
public import Unfoldings.Roof.HorizontalGraphAbove

/-! The actual two-link closing graph supplies the complete long-link normal trace. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Filter Topology Real InnerProductGeometry PlanarTopology RegularClosingLink

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

local notation "east" => (WithLp.toLp 2 ![(1 : ℝ), 0] : Plane)

theorem eq_of_horizontal_segment_point {p q z : Plane} (horizontal : q 1 = p 1)
    (member : z ∈ segment ℝ p q) : z 1 = p 1 := by
  obtain ⟨t, _, rfl⟩ := (segment_eq_image_lineMap ℝ p q).subset member
  rw [AffineMap.lineMap_apply_module']
  change t * (q 1 - p 1) + p 1 = p 1
  rw [horizontal, sub_self, mul_zero, zero_add]

/-- Until the bend, the graph follows the horizontal long link. -/
theorem graphClosing_value_of_before_bend {g : ℝ → ℝ} {a c b : Plane}
    (first : a 0 < c 0) (last : c 0 < b 0) (horizontal : c 1 = a 1)
    (trace : graphPoint g '' Set.Icc (a 0) (b 0) = segment ℝ a c ∪ segment ℝ c b)
    {x : ℝ} (window : x ∈ Set.Icc (a 0) (b 0)) (early : x ≤ c 0) : g x = a 1 := by
  rcases trace.subset (Set.mem_image_of_mem (graphPoint g) window) with left | right
  · exact eq_of_horizontal_segment_point horizontal left
  · have right_x := (horizontal_mem_Icc_of_mem_segment last.le right).1
    have h : x = c 0 := le_antisymm early right_x
    have at_c : c ∈ graphPoint g '' Set.Icc (a 0) (b 0) :=
      trace.symm.subset (Or.inl (right_mem_segment ℝ _ _))
    obtain ⟨t, _, eq⟩ := at_c
    have xt : t = c 0 := congrArg (fun p : Plane => p 0) eq
    have yt : g t = c 1 := congrArg (fun p : Plane => p 1) eq
    rwa [h, ← xt, ← horizontal]

open Classical in
set_option maxHeartbeats 2200000 in
/-- The signed sum on the actual long link equals its supported normal
transport. The short link has one support, leaving only the one bend error. -/
theorem exists_horizontalClosingGraph_trace {g : ℝ → ℝ} (hg : Continuous g)
    {a c b : Plane} (first : a 0 < c 0) (last : c 0 < b 0) (horizontal : c 1 = a 1)
    (trace : graphPoint g '' Set.Icc (a 0) (b 0) = segment ℝ a c ∪ segment ℝ c b)
    (inside : graphPoint g '' Set.Icc (a 0) (b 0) ⊆ interior K.footprint)
    (sample : Face → Plane) (sample_in : ∀ i, sample i ∈ interior (K.projectedTriangle i).carrier)
    (endpoints : ∀ i z, z ∈ interior (K.projectedTriangle i).carrier → z 0 ≠ a 0 ∧ z 0 ≠ b 0)
    (aligned : ∀ i, Disjoint (interior (K.projectedTriangle i).carrier)
      (graphPoint g '' Set.Icc (a 0) (b 0)))
    (first_regular : ∀ w : C.Vertex Set.univ, K.projectedVertex w ∈ openSegment ℝ a c →
      K.HasRegularSectionSlopes w (c - a))
    (start bend middle : C.Vertex Set.univ) (marked_start : K.projectedVertex start = a)
    (marked_bend : K.projectedVertex bend = c) (on_middle : K.projectedVertex middle ∈ openSegment ℝ a c)
    (f : Face)
    (flat : ∀ w : C.Vertex Set.univ, K.projectedVertex w ∈ segment ℝ c b → K.projectedVertex w ≠ b →
      ∀ j i, C.vertexOfCorner Set.univ (j, i) = w → K.normalSlope j = K.normalSlope f)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ)
    {cell : Set Plane} (slopes : ∀ i, K.normalSlope i ∈ cell) :
    ∃ (m : ℕ) (T : K.SupportedNormalTrace cell (a 1) (m + 1)) (initial : C.Germ) (t : ℝ),
      0 < t ∧ K.projectedGermStart initial = horizontalContactPoint a t ∧
      K.projectedGermFinish initial = a ∧
      T.path.vertex 0 = K.normalSlope initial.1.1 ∧
      T.path.vertex (Fin.last (m + 1)) = K.normalSlope f ∧
      |(∑ v : C.Vertex Set.univ, if K.projectedVertex v ∈ graphPoint g '' Set.Ioo (a 0) (b 0) then
        K.regionalAngleExcess (facesAboveGraph sample g (a 0) (b 0)) v else 0) + T.hingeSum| ≤
        |angle (K.sectionDirection f (c - a)) (K.sectionDirection f (b - c)) - angle (c - a) (b - c)| := by
  let len := c 0 - a 0
  have len_pos : 0 < len := sub_pos.mpr first
  have wave : c - a = len • east := by
    ext i
    fin_cases i
    · change c 0 - a 0 = len * 1
      rw [mul_one]
    · change c 1 - a 1 = len * 0
      rw [horizontal, sub_self, mul_zero]
  have east_unit : ‖east‖ = 1 := by
    rw [show east = EuclideanSpace.single 0 1 by ext i; fin_cases i <;> rfl]
    simp [EuclideanSpace.single]
  have len_eq : ‖c - a‖ = len := by rw [wave, norm_smul, Real.norm_eq_abs, abs_of_pos len_pos, east_unit, mul_one]
  have direction : NormedSpace.normalize (c - a) = east := by
    rw [NormedSpace.normalize, len_eq, wave, smul_smul, inv_mul_cancel₀ len_pos.ne', one_smul]
  have c_at : horizontalContactPoint a len = c := by
    unfold horizontalContactPoint
    rw [← wave]
    abel
  have closed_segment (p q : Plane) : IsClosed (segment ℝ p q) := by
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
  have separate {p q r : Plane} (pq : p 0 < q 0) (qr : q 0 < r 0) :
      Disjoint (openSegment ℝ p q) (segment ℝ q r) := by
    apply Set.disjoint_left.mpr
    intro z hp hq
    exact (horizontal_mem_Ioo_of_mem_openSegment pq hp).2.not_ge
      (horizontal_mem_Icc_of_mem_segment qr.le hq).1
  obtain ⟨L, times, actual, turns⟩ :=
    K.exists_regularClosingLink_on_graphSegment hg sample sample_in endpoints aligned inside
      first le_rfl last.le (fun _ hx => trace.symm.subset (Or.inl hx))
      (segment ℝ c b) (closed_segment c b) trace.subset (separate first last) first_regular
  revert L times actual turns
  rw [direction, len_eq]
  rintro L times actual turns
  let U := facesAboveGraph sample g (a 0) (b 0)
  let I := {w : C.Vertex Set.univ // K.projectedVertex w ∈ openSegment ℝ a c}
  let J := {w : C.Vertex Set.univ // K.projectedVertex w ∈ openSegment ℝ c b}
  have above (i : I) (r : C.LinkGerm Set.univ
      (C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ (L.bank i))))
      (hr : r.val.1.1 ∈ U) : 0 ≤ K.projectedGermRay r 1 := by
    apply K.projectedGermRay_transverse_nonneg_of_above_horizontal hg sample sample_in endpoints aligned r hr
    rw [L.vertexAt_contact]
    have at_x : (horizontalContactPoint a (L.time i)) 0 ∈ Set.Ioo (a 0) (c 0) := by
      change a 0 < a 0 + L.time i * 1 ∧ a 0 + L.time i * 1 < c 0
      have ht := times i
      change 0 < L.time i ∧ L.time i < c 0 - a 0 at ht
      constructor <;> linarith only [ht.1, ht.2]
    filter_upwards [isOpen_Ioo.mem_nhds at_x] with x hx
    have y : (horizontalContactPoint a (L.time i)) 1 = a 1 := by
      change a 1 + L.time i * 0 = a 1
      rw [mul_zero, add_zero]
    rw [y]
    exact graphClosing_value_of_before_bend first last horizontal trace
      ⟨hx.1.le, (hx.2.trans last).le⟩ hx.2.le
  obtain ⟨m, T, initial, terminal, t, u, tp, up, i_start, i_finish, t_start, t_finish,
    t_first, t_last, sum_turns⟩ :=
    L.exists_complete_supportedNormalTrace ⟨⟨middle, on_middle⟩⟩ c_at
      times actual start bend (by simpa [horizontalContactPoint] using marked_start)
      (marked_bend.trans c_at.symm) above slopes
  rw [c_at] at t_finish
  have terminal_corner :
      C.vertexOfCorner Set.univ (terminal.1.1, (C.germFarCorner terminal).2) = bend := by
    apply K.projectedVertex_injective
    rw [K.projectedVertex_ofCorner, marked_bend]
    exact t_finish
  have last_normal : T.path.vertex (Fin.last (m + 1)) = K.normalSlope f :=
    t_last.trans (flat bend (marked_bend.symm ▸ left_mem_segment ℝ c b)
      (fun h => last.ne (congrArg (fun p : Plane => p 0) (marked_bend.symm.trans h)))
      _ _ terminal_corner)
  have no_over : Disjoint (openSegment ℝ c b) (segment ℝ a c) := by
    apply Set.disjoint_left.mpr
    intro z on off
    exact (horizontal_mem_Ioo_of_mem_openSegment last on).1.not_ge
      (horizontal_mem_Icc_of_mem_segment first.le off).2
  have short_regular (w : C.Vertex Set.univ) (h : K.projectedVertex w ∈ openSegment ℝ c b) :
      K.HasRegularSectionSlopes w (b - c) := by
    have nb : K.projectedVertex w ≠ b := by
      intro hb
      exact (horizontal_mem_Ioo_of_mem_openSegment last h).2.ne (congrArg (fun p : Plane => p 0) hb)
    exact ⟨K.normalSlope f, K.normalSlope f, fun j i hw => Or.inl
      (flat w (openSegment_subset_segment ℝ _ _ h) nb j i hw), Or.inl rfl⟩
  obtain ⟨S, _, s_actual, s_turns⟩ :=
    K.exists_regularClosingLink_on_graphSegment hg sample sample_in endpoints aligned inside
      last first.le le_rfl (fun _ hx => trace.symm.subset (Or.inr hx))
      (segment ℝ a c) (closed_segment a c) (by rw [trace, Set.union_comm]) no_over short_regular
  have short_ne : b - c ≠ 0 := sub_ne_zero.mpr
    (fun eq => last.ne (congrArg (fun p : Plane => p 0) eq.symm))
  have direction_ne : NormedSpace.normalize (b - c) ≠ 0 := by
    intro h
    have unit := NormedSpace.norm_normalize short_ne
    rw [h, norm_zero] at unit
    exact zero_ne_one unit
  have flat_short (j : J) : K.regionalAngleExcess U j.val = 0 := by
    let e := S.bank j
    let q := (C.restrictFaces U).boundaryMate Set.univ e
    have at_e : C.vertexOfCorner Set.univ (e.val.1.1.val, e.val.1.2) = j.val := by
      apply K.projectedVertex_injective
      rw [K.projectedVertex_ofCorner, s_actual]
      have p := S.position j
      rwa [(K.folding.restrictFaces U).boundaryPosition_raw] at p
    have at_q : C.vertexOfCorner Set.univ (q.val.1.1.val, q.val.1.2) = j.val := by
      apply K.projectedVertex_injective
      rw [← at_e, K.projectedVertex_ofCorner, K.projectedVertex_ofCorner]
      have eq := (K.folding.restrictFaces U).boundaryPosition_mate e
      have xy := congrArg Cap.horizontal eq
      rwa [(K.folding.restrictFaces U).boundaryPosition_raw,
        (K.folding.restrictFaces U).boundaryPosition_raw] at xy
    have nb : K.projectedVertex j.val ≠ b := by
      intro hb
      exact (horizontal_mem_Ioo_of_mem_openSegment last j.property).2.ne (congrArg (fun p : Plane => p 0) hb)
    have e_slope := flat j.val (openSegment_subset_segment ℝ _ _ j.property) nb _ _ at_e
    have q_slope := flat j.val (openSegment_subset_segment ℝ _ _ j.property) nb _ _ at_q
    have zero := S.abs_turnError_le nonnegative small tilt j
    change |K.restrictedBoundaryTurnError U e| ≤ sin φ *
      angle (K.sectionDirection e.val.1.1.val (NormedSpace.normalize (b - c)))
        (K.sectionDirection q.val.1.1.val (NormedSpace.normalize (b - c))) at zero
    rw [show K.sectionDirection e.val.1.1.val (NormedSpace.normalize (b - c)) =
        K.sectionDirection q.val.1.1.val (NormedSpace.normalize (b - c)) by
      simp only [sectionDirection, e_slope, q_slope],
      angle_self (K.sectionDirection_ne_zero _ direction_ne), mul_zero, s_turns j, abs_neg] at zero
    exact abs_nonpos_iff.mp zero
  let G := K.regionalAngleExcess U
  let dom := graphPoint g '' Set.Ioo (a 0) (b 0)
  have bend_ne_left : K.projectedVertex bend ∉ openSegment ℝ a c := by
    intro h
    exact (horizontal_mem_Ioo_of_mem_openSegment first h).2.ne
      (congrArg (fun p : Plane => p 0) marked_bend)
  have bend_ne_right : K.projectedVertex bend ≠ b := by
    intro equal
    exact last.ne (congrArg (fun p : Plane => p 0) (marked_bend.symm.trans equal))
  have eq_term (v : C.Vertex Set.univ) :
      (if K.projectedVertex v ∈ dom then G v else 0) =
      (if K.projectedVertex v ∈ openSegment ℝ a c then G v else 0) + (if v = bend then G bend else 0) := by
    have at_bend : K.projectedVertex v = c ↔ v = bend := by
      rw [← marked_bend, K.projectedVertex_injective.eq_iff]
    have in_dom : K.projectedVertex v ∈ dom ↔ (K.projectedVertex v ∈ openSegment ℝ a c ∨
        K.projectedVertex v ∈ openSegment ℝ c b) ∨ v = bend := by
      simp only [dom, graphPoint_openWindow_eq_twoLinks first last trace, Set.mem_union,
        Set.mem_singleton_iff, at_bend]
    by_cases eq : v = bend
    · subst v
      simp [in_dom, bend_ne_left]
    by_cases hl : K.projectedVertex v ∈ openSegment ℝ a c
    · simp [in_dom, hl, eq]
    by_cases hr : K.projectedVertex v ∈ openSegment ℝ c b
    · simp [in_dom, hl, hr, eq, show G v = 0 from flat_short ⟨v, hr⟩]
    · simp [in_dom, hl, hr, eq]
  have sum_i : (∑ v : C.Vertex Set.univ, if K.projectedVertex v ∈ openSegment ℝ a c then G v else 0) =
      ∑ i : I, G i.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp [I]) _
  have signed : (∑ i : I, G i.val) = -T.hingeSum := by
    rw [sum_turns, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [turns i, neg_neg]
  refine ⟨m, T, initial, t, tp, i_start, ?_, t_first, last_normal, ?_⟩
  · simpa [horizontalContactPoint] using i_finish
  · change |(∑ v : C.Vertex Set.univ, if K.projectedVertex v ∈ dom then G v else 0) + T.hingeSum| ≤ _
    simp only [eq_term, Finset.sum_add_distrib, sum_i, signed, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    rw [show -T.hingeSum + G bend + T.hingeSum = G bend by abel]
    exact (K.abs_graphClosingBend_excess_eq hg first last trace sample sample_in endpoints
      aligned bend marked_bend (inside (trace.symm.subset (Or.inl (right_mem_segment ℝ _ _))))
      f (flat bend (marked_bend.symm ▸ left_mem_segment ℝ _ _) bend_ne_right)).le

end Unfoldings.ConvexRoof
