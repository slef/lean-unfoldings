module

public import Unfoldings.Roof.ClosingBendLimit
public import Unfoldings.Geometry.ShortClosingTail

/-! A regular closing bend with a short terminal link and a curvature-free tail. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Filter Topology InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Choose the bend near the terminal endpoint. The axis along the long link
controls the full chain, and the portion of the chain beyond the bend stays
inside the requested terminal neighborhood. -/
theorem exists_regular_shortClosing_bend {n : ℕ} (P : PolygonalChain Plane n) (n_pos : 0 < n)
    (acute : ∀ i, 0 < inner ℝ (P.vertex (Fin.last n) - P.vertex 0) (P.edge i))
    {I J : Type*} [Finite I] [Finite J] (point : I → Plane) (edge : J → Plane →ᵃ[ℝ] ℝ)
    (proper : ∀ j, edge j ≠ 0) (first : ∀ i, P.vertex 0 ≠ point i)
    (last : ∀ i, P.vertex (Fin.last n) ≠ point i) {D : Set Plane}
    (opened : IsOpen D) (a_in : P.vertex 0 ∈ D) (b_in : P.vertex (Fin.last n) ∈ D)
    {r η : ℝ} (rp : 0 < r) (ηp : 0 < η) :
    let a := P.vertex 0
    let b := P.vertex (Fin.last n)
    ∃ c ∈ D ∩ Metric.ball b r,
      (∀ i, 0 < inner ℝ (c - a) (P.edge i)) ∧
      0 < inner ℝ (c - a) (b - c) ∧
      (∀ j, edge j c ≠ 0) ∧
      (∀ (j : Fin 2) (t : ℝ) i,
        AffineMap.lineMap (P.twoClosingLinks c j).1 (P.twoClosingLinks c j).2 t ≠ point i) ∧
      (Set.range P.path ∩ Set.range (P.forwardClosingChain c).path).Finite ∧
      (∀ p ∈ Set.range P.path, inner ℝ (c - a) c ≤ inner ℝ (c - a) p → p ∈ Metric.ball b r) ∧
      angle (c - a) (b - c) < η ∧
      ∀ f : Face, |angle (K.sectionDirection f (c - a)) (K.sectionDirection f (b - c)) -
        angle (c - a) (b - c)| < η := by
  classical
  let a := P.vertex 0
  let b := P.vertex (Fin.last n)
  let h := innerSL ℝ (b - a)
  let j : Fin n := ⟨n - 1, by omega⟩
  let v := P.vertex j.castSucc
  have h_progress : ∀ i, 0 < h (P.edge i) := acute
  have mono := P.strictMono_linear_vertices h h_progress
  have ordered : h a < h b := mono (show (0 : Fin (n + 1)) < Fin.last n from n_pos)
  have different : a ≠ b := fun eq => ordered.ne (congrArg h eq)
  have finish : j.succ = Fin.last n := by apply Fin.ext; change n - 1 + 1 = n; omega
  have step : h v < h b := by
    have hh := h_progress j
    rw [PolygonalChain.edge, map_sub, finish] at hh
    exact sub_pos.mp hh
  obtain ⟨d, db, d_mem⟩ := P.exists_terminal_segment_point_near n_pos Metric.isOpen_ball (Metric.mem_ball_self rp)
  change d ∈ openSegment ℝ v b at d_mem
  have dl : h d < h b := by
    have im := Set.mem_image_of_mem h.toLinearMap d_mem
    change h d ∈ h.toLinearMap.toAffineMap '' openSegment ℝ v b at im
    rw [image_openSegment ℝ h.toLinearMap.toAffineMap] at im
    change h d ∈ openSegment ℝ (h v) (h b) at im
    rw [openSegment_eq_Ioo step] at im
    exact im.2
  let U := D ∩ Metric.ball b r ∩ {p | h d < h p}
  have u_open : IsOpen U :=
    (opened.inter Metric.isOpen_ball).inter (isOpen_lt continuous_const h.continuous)
  have b_U : b ∈ U := ⟨⟨b_in, Metric.mem_ball_self rp⟩, dl⟩
  have b_closure : b ∈ closure (openSegment ℝ a b) :=
    segment_subset_closure_openSegment (right_mem_segment ℝ a b)
  obtain ⟨c₀, c₀_in, c₀_seg⟩ := mem_closure_iff_nhds.mp b_closure U (u_open.mem_nhds b_U)
  obtain ⟨t, ht, at_t⟩ := (openSegment_eq_image_lineMap ℝ a b).subset c₀_seg
  have left : c₀ - a = t • (b - a) := by
    rw [← at_t, AffineMap.lineMap_apply_module']; abel
  have right : b - c₀ = (1 - t) • (b - a) := by
    rw [← at_t, AffineMap.lineMap_apply_module', sub_smul, one_smul]
    abel
  have left_ne : c₀ - a ≠ 0 := by
    rw [left]; exact smul_ne_zero ht.1.ne' (sub_ne_zero.mpr different.symm)
  have right_ne : b - c₀ ≠ 0 := by
    rw [right]; exact smul_ne_zero (sub_pos.mpr ht.2).ne' (sub_ne_zero.mpr different.symm)
  have proportional : b - c₀ = ((1 - t) / t) • (c₀ - a) := by
    rw [left, right, smul_smul, div_mul_cancel₀ _ ht.1.ne']
  have pointwise (z : Plane) : inner ℝ (c₀ - a) z = t * h z := by
    rw [left, real_inner_smul_left]
    rfl
  have at_progress (i : Fin n) : 0 < inner ℝ (c₀ - a) (P.edge i) := by
    rw [pointwise]
    exact mul_pos ht.1 (h_progress i)
  have at_right : 0 < inner ℝ (c₀ - a) (b - c₀) := by
    rw [proportional, real_inner_smul_right, real_inner_self_eq_norm_sq]
    exact mul_pos (div_pos (sub_pos.mpr ht.2) ht.1) (pow_pos (norm_pos_iff.mpr left_ne) 2)
  have at_tail : inner ℝ (c₀ - a) d < inner ℝ (c₀ - a) c₀ := by
    rw [pointwise d, pointwise c₀]
    exact mul_lt_mul_of_pos_left c₀_in.2 ht.1
  let coord (c z : Plane) : ℝ := inner ℝ (c - a) z
  have cp : ∀ᶠ c in 𝓝 c₀, ∀ i, 0 < coord c (P.edge i) := by
    apply Filter.eventually_all.mpr
    intro i
    have cont : Continuous (fun c => coord c (P.edge i)) := by unfold coord; fun_prop
    exact (isOpen_lt continuous_const cont).mem_nhds (at_progress i)
  have cr : ∀ᶠ c in 𝓝 c₀, 0 < coord c (b - c) := by
    have cont : Continuous (fun c => coord c (b - c)) := by unfold coord; fun_prop
    exact (isOpen_lt continuous_const cont).mem_nhds at_right
  have ct : ∀ᶠ c in 𝓝 c₀, coord c d < coord c c := by
    have c₁ : Continuous (fun c => coord c d) := by unfold coord; fun_prop
    have c₂ : Continuous (fun c => coord c c) := by unfold coord; fun_prop
    exact (isOpen_lt c₁ c₂).mem_nhds at_tail
  have turning : ∀ᶠ c in 𝓝 c₀, angle (c - a) (b - c) < η := by
    have c₁ : ContinuousAt (fun c : Plane => c - a) c₀ := continuousAt_id.sub continuousAt_const
    have c₂ : ContinuousAt (fun c : Plane => b - c) c₀ := continuousAt_const.sub continuousAt_id
    have ang := (continuousAt_angle left_ne right_ne).comp
      (f := fun c : Plane => (c - a, b - c)) (c₁.prodMk c₂)
    change Tendsto (fun c : Plane => angle (c - a) (b - c)) (𝓝 c₀)
      (𝓝 (angle (c₀ - a) (b - c₀))) at ang
    have value : angle (c₀ - a) (b - c₀) = 0 := by
      rw [proportional, angle_smul_right_of_pos _ _ (div_pos (sub_pos.mpr ht.2) ht.1), angle_self left_ne]
    rw [value] at ang
    exact ang.eventually (gt_mem_nhds ηp)
  have bend : ∀ᶠ c in 𝓝 c₀, ∀ f : Face,
      |angle (K.sectionDirection f (c - a)) (K.sectionDirection f (b - c)) -
        angle (c - a) (b - c)| < η :=
    Filter.eventually_all.mpr (fun f =>
      (K.tendsto_closingBend_angleError_of_positive_collinear f left_ne
        (div_pos (sub_pos.mpr ht.2) ht.1) proportional).eventually (gt_mem_nhds ηp))
  have inside : ∀ᶠ c in 𝓝 c₀, c ∈ D ∩ Metric.ball b r :=
    (opened.inter Metric.isOpen_ball).mem_nhds c₀_in.1
  have good : ∀ᶠ c in 𝓝 c₀, c ∈ D ∩ Metric.ball b r ∧
      (∀ i, 0 < coord c (P.edge i)) ∧ 0 < coord c (b - c) ∧ coord c d < coord c c ∧
      angle (c - a) (b - c) < η ∧ ∀ f : Face,
        |angle (K.sectionDirection f (c - a)) (K.sectionDirection f (b - c)) -
          angle (c - a) (b - c)| < η := by
    filter_upwards [inside, cp, cr, ct, turning, bend] with c hc hp hr ht ht' hb
    exact ⟨hc, hp, hr, ht, ht', hb⟩
  obtain ⟨δ, δp, controls⟩ := Metric.eventually_nhds_iff_ball.mp good
  have x_c₀ : h c₀ = t * (h b - h a) + h a := by
    rw [← at_t, AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul]
  have left_x : h a < h c₀ := by rw [x_c₀]; linarith only [mul_pos ht.1 (sub_pos.mpr ordered)]
  have right_x : h c₀ < h b := by
    rw [x_c₀]
    nlinarith only [mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr ordered)]
  obtain ⟨c, ball, _, _, generic, no_vertex, finite⟩ :=
    P.exists_regular_nearChord_apex_of_ordered h point edge proper first last
      Metric.isOpen_ball ⟨c₀, Metric.mem_ball_self δp, left_x, right_x⟩
  obtain ⟨c_in, progress, end_progress, tail, turn, error⟩ := controls c ball
  refine ⟨c, c_in, progress, end_progress, generic, no_vertex, ?_, ?_, turn, error⟩
  · rw [P.forwardClosingChain_trace]
    exact finite
  · intro p here passed
    let k := innerSL ℝ (c - a)
    have k_progress (i : Fin n) : 0 < k (P.edge i) := progress i
    have after : k d ≤ k p := tail.le.trans passed
    have side := P.mem_terminal_subsegment_of_coord_ge n_pos k k_progress
      (openSegment_subset_segment ℝ v b d_mem) here after
    exact (convex_ball b r).segment_subset db (Metric.mem_ball_self rp) side

end Unfoldings.ConvexRoof
