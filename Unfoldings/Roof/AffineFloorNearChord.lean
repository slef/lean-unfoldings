module

public import Unfoldings.Roof.AffineFloorChartClosingMesh
public import Unfoldings.Roof.AffineFloorChartSkeleton
public import Unfoldings.Roof.GraphBankSharpBudget
public import Unfoldings.Roof.ClosingBendLimit
public import Unfoldings.Geometry.TwoGraphEndpointRays

/-! Close an actual coarse bank with a two-link graph and account for each turn on the same roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.FloorMesh

open Filter Topology Real InnerProductGeometry PlanarTopology

universe u

variable {I J : Type u} [Fintype I] [Nonempty I]
  {family : I → SpatialPlane} {floor : Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (T : FloorMesh family floor extra Z)
  (E : Plane ≃ₗᵢ[ℝ] Plane) {n : ℕ} (P : PolygonalChain Plane (n + 1))
  (inside : (interior (clipAbove family floor Z)).Nonempty)

local notation "A" => P.vertex 0
local notation "B" => P.vertex (Fin.last (n + 1))
local notation "L[" c "]" => chartClosingMesh T E P c inside
local notation "Q[" c "]" => chartClosingRoof T E P c inside
local notation "D" => interior (E '' clipAbove family floor Z)
local notation "X" => EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0

local instance oldChartIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite
local instance nearChordChartIndexFintype (c : Plane) : Fintype (L[c]).mesh.Index :=
  @Fintype.ofFinite _ (L[c]).mesh.finite

private theorem local_first_ray_in_trace : ∀ᶠ t : ℝ in 𝓝[>] 0,
    (A) + t • P.edge 0 ∈ Set.range P.path := by
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
  rw [P.path_range_eq_segments]
  right
  refine Set.mem_iUnion.mpr ⟨(0 : Fin (n + 1)), ?_⟩
  have position : AffineMap.lineMap (P.vertex (Fin.castSucc (0 : Fin (n + 1))))
      (P.vertex (0 : Fin (n + 1)).succ) t = (A) + t • P.edge 0 := by
    rw [AffineMap.lineMap_apply_module']
    exact add_comm _ _
  rw [← position]
  exact lineMap_mem_segment ℝ _ _ ⟨ht.1.le, ht.2.le⟩

private theorem local_last_ray_in_trace : ∀ᶠ t : ℝ in 𝓝[>] 0,
    (B) + t • (-P.edge (Fin.last n)) ∈ Set.range P.path := by
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
  rw [P.path_range_eq_segments]
  right
  refine Set.mem_iUnion.mpr ⟨Fin.last n, ?_⟩
  have tail_eq : P.vertex (Fin.last n).succ = (B) := by simp only [Fin.succ_last]
  have direction : -P.edge (Fin.last n) = P.vertex (Fin.last n).castSucc - (B) := by
    rw [PolygonalChain.edge, neg_sub, tail_eq]
  rw [tail_eq, direction]
  rw [segment_symm ℝ (P.vertex (Fin.last n).castSucc) (B)]
  have position : AffineMap.lineMap (B) (P.vertex (Fin.last n).castSucc) t =
      (B) + t • (P.vertex (Fin.last n).castSucc - (B)) := by
    rw [AffineMap.lineMap_apply_module']
    exact add_comm _ _
  rw [← position]
  exact lineMap_mem_segment ℝ _ _ ⟨ht.1.le, ht.2.le⟩

private theorem regular_forward_links (c : Plane)
    (regular : ∀ (j : Fin 2) (t : ℝ) i, AffineMap.lineMap (P.twoClosingLinks c j).1
      (P.twoClosingLinks c j).2 t ≠ T.chartCorner E i) :
    (∀ (t : ℝ) (i : T.Index) (j : Fin 3), AffineMap.lineMap (A) c t ≠ T.chartCorner E (i, j)) ∧
    (∀ (t : ℝ) (i : T.Index) (j : Fin 3), AffineMap.lineMap c (B) t ≠ T.chartCorner E (i, j)) := by
  constructor
  · intro t i j
    have h := regular 1 (1 - t) (i, j)
    change AffineMap.lineMap c (A) (1 - t) ≠ _ at h
    rwa [AffineMap.lineMap_apply_one_sub] at h
  · intro t i j
    have h := regular 0 (1 - t) (i, j)
    change AffineMap.lineMap (B) c (1 - t) ≠ _ at h
    rwa [AffineMap.lineMap_apply_one_sub] at h

open Classical in
set_option maxHeartbeats 2200000 in
/-- At any tolerance, construct one physical comparison roof and bound the
actual fixed-bank sum on both sides. The excess beyond the limiting budget
comes only from the auxiliary bend and the link-direction mismatch. -/
theorem exists_chartComparison_nearChord
    (progress : ∀ i, 0 < (P.edge i) 0) (in_domain : Set.range P.path ⊆ D)
    (skeleton : Set.range P.path ⊆ ⋃ i : T.Index × Fin 3,
      segment ℝ (T.chartCorner E i) (T.chartCorner E (i.1, Triangle.next i.2)))
    (first : ∀ i, (A) ≠ T.chartCorner E i) (last : ∀ i, (B) ≠ T.chartCorner E i)
    {φ η : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2)
    (fine_tilt : ∀ c, (Q[c]).TiltBound φ) (tolerance : 0 < η) :
    ∃ (c : Plane) (f : ℝ → ℝ) (sample : (L[c]).mesh.Index → Plane),
      Continuous f ∧ graphPoint f '' Set.Icc ((A) 0) ((B) 0) = Set.range P.path ∧
      (∀ j, sample j ∈ interior ((Q[c]).projectedTriangle j).carrier) ∧
      ∀ right : Bool, |(Q[c]).graphBankAngleSum f sample ((A) 0) ((B) 0) right| ≤
        (L[c]).mesh.pairedComplex.totalInteriorAngularDefect Set.univ +
          2 * (2 * arcsin (tan (φ / 2) ^ 2)) + 2 * φ * sin φ + (1 + sin φ * tan φ) * η := by
  let K := (T.roof inside).reorient E
  let : Finite T.Index := T.finite
  have convex : Convex ℝ D :=
    ((convex_clipAbove family floor Z).linear_image E.toLinearEquiv.toLinearMap).interior
  have A_in : (A) ∈ D := in_domain (P.vertex_mem_path_range 0)
  have B_in : (B) ∈ D := in_domain (P.vertex_mem_path_range (Fin.last (n + 1)))
  have mid := convex.midpoint_mem A_in B_in
  obtain ⟨c, c_in, progress_g, no_edge, no_corner, finite, mismatch, small_bend⟩ :=
    K.exists_regular_closing_with_small_bend P (by omega) progress (T.chartCorner E)
      (T.chartEdgeEquation E) (T.chartEdgeEquation_ne_zero E) first last
      isOpen_interior mid tolerance
  let G := P.forwardClosingChain c
  have first_progress : (A) 0 < c 0 := sub_pos.mp (progress_g 0)
  have last_progress : c 0 < (B) 0 := sub_pos.mp (progress_g 1)
  have ordered := first_progress.trans last_progress
  have g_range : Set.range G.path = segment ℝ (A) c ∪ segment ℝ c (B) := by
    rw [P.forwardClosingChain_trace c, segment_symm ℝ (B) c, segment_symm ℝ c (A), Set.union_comm]
  have G_in : Set.range G.path ⊆ D := by
    rw [g_range]
    exact Set.union_subset (convex.segment_subset A_in c_in) (convex.segment_subset c_in B_in)
  obtain ⟨f, hf, f_vertex, f_range⟩ :=
    P.exists_continuous_graph_of_horizontal (by omega) progress
  obtain ⟨g, hg, g_vertex, g_range'⟩ :=
    G.exists_continuous_graph_of_horizontal (by omega) progress_g
  change graphPoint g '' Set.Icc ((A) 0) ((B) 0) = Set.range G.path at g_range'
  have start : f ((A) 0) = g ((A) 0) := (f_vertex 0).trans (g_vertex 0).symm
  have finish : f ((B) 0) = g ((B) 0) :=
    (f_vertex (Fin.last (n + 1))).trans (g_vertex (Fin.last 2)).symm
  have contacts : {t ∈ Set.Icc ((A) 0) ((B) 0) | f t = g t}.Finite := by
    apply (finite.image (X)).subset
    rintro t ⟨interval, agree⟩
    refine ⟨graphPoint f t, ⟨f_range.subset ⟨t, interval, rfl⟩, ?_⟩, rfl⟩
    exact g_range'.subset ⟨t, interval, by simp only [graphPoint, agree]⟩
  let L := L[c]
  let Q := Q[c]
  have footprint : Q.footprint = E '' clipAbove family floor Z :=
    chartClosingRoof_footprint T E P c inside
  have contained :
      (graphPoint f '' Set.Icc ((A) 0) ((B) 0)) ∪
        (graphPoint g '' Set.Icc ((A) 0) ((B) 0)) ⊆ interior Q.footprint := by
    rw [f_range, g_range', footprint]
    exact Set.union_subset in_domain G_in
  let sample (j : L.mesh.Index) := (Q.projectedTriangle j).interior_nonempty.some
  have sample_in (j : L.mesh.Index) : sample j ∈ interior (Q.projectedTriangle j).carrier :=
    (Q.projectedTriangle j).interior_nonempty.some_mem
  have endpoints (j : L.mesh.Index) (p : Plane)
      (h : p ∈ interior (Q.projectedTriangle j).carrier) : p 0 ≠ (A) 0 ∧ p 0 ≠ (B) 0 :=
    chartClosingRoof_interior_avoids_endLines T E P c inside j h
  have aligned_f (j : L.mesh.Index) : Disjoint (interior (Q.projectedTriangle j).carrier)
      (graphPoint f '' Set.Icc ((A) 0) ((B) 0)) := by
    rw [f_range]
    exact (chartClosingRoof_disjoint_paths T E P c inside j).mono_right Set.subset_union_left
  have aligned_g (j : L.mesh.Index) : Disjoint (interior (Q.projectedTriangle j).carrier)
      (graphPoint g '' Set.Icc ((A) 0) ((B) 0)) := by
    rw [g_range']
    exact (chartClosingRoof_disjoint_paths T E P c inside j).mono_right Set.subset_union_right
  have mark (i : Fin 3) (h : closingMark P c i ∈ D) :
      ∃ w : L.mesh.pairedComplex.Vertex Set.univ, Q.projectedVertex w = closingMark P c i :=
    exists_chartClosingRoof_markedVertex T E P c inside i (footprint.symm ▸ interior_subset h)
  obtain ⟨left, at_left⟩ := mark 0 A_in
  obtain ⟨right, at_right⟩ := mark 1 B_in
  obtain ⟨bend, at_bend⟩ := mark 2 c_in
  change Q.projectedVertex left = (A) at at_left
  change Q.projectedVertex right = (B) at at_right
  change Q.projectedVertex bend = c at at_bend
  have first_graph : Q.projectedVertex left = graphPoint f ((A) 0) := by
    rw [at_left]
    apply PiLp.ext
    intro i
    fin_cases i
    · rfl
    · exact (f_vertex 0).symm
  have last_graph : Q.projectedVertex right = graphPoint f ((B) 0) := by
    rw [at_right]
    apply PiLp.ext
    intro i
    fin_cases i
    · rfl
    · exact (f_vertex (Fin.last (n + 1))).symm
  obtain ⟨s₁, s₂, slopes_left, tangent_left⟩ := L.exists_tangentSlopes_of_chart_ray
    E inside left (P.edge 0) (fun i => at_left ▸ first i)
    (at_left.symm ▸ (local_first_ray_in_trace P).mono (fun _ h => skeleton h))
  obtain ⟨t₁, t₂, slopes_right, tangent_right⟩ := L.exists_tangentSlopes_of_chart_ray
    E inside right (-P.edge (Fin.last n)) (fun i => at_right ▸ last i)
    (at_right.symm ▸ (local_last_ray_in_trace P).mono (fun _ h => skeleton h))
  have rays_left := P.eventually_mem_union_forwardChains_iff_initial_rays G (X)
    progress progress_g rfl
  have rays_right := P.eventually_mem_union_forwardChains_iff_terminal_rays G (X)
    progress progress_g rfl
  have bend_dom : E.symm c ∈ clipAbove family floor Z := by
    obtain ⟨q, hq, equal⟩ := interior_subset c_in
    change E q = c at equal
    rw [← equal, E.symm_apply_apply]
    exact hq
  obtain ⟨old_face, old_interior⟩ := T.exists_original_interior_of_chart_regular E bend_dom no_edge
  have physical_bend : (L.mesh.roof inside).projectedVertex bend = E.symm c := by
    apply E.injective
    rw [E.apply_symm_apply]
    change ((L.mesh.roof inside).reorient E).projectedVertex bend = c at at_bend
    rwa [ConvexRoof.projectedVertex_reorient] at at_bend
  have slope_at_bend (j : L.mesh.Index) (i : Fin 3)
      (h : L.mesh.pairedComplex.vertexOfCorner Set.univ (j, i) = bend) :
      Q.normalSlope j = K.normalSlope old_face :=
    L.chart_slope_eq_of_mem_original_interior inside E bend old_face (physical_bend.symm ▸ old_interior) j i h
  obtain ⟨⟨f_bend, i_bend⟩, vertex_bend⟩ := L.mesh.pairedComplex.vertexOfCorner_surjective Set.univ bend
  have only_bend (j : L.mesh.Index) (i : Fin 3)
      (h : L.mesh.pairedComplex.vertexOfCorner Set.univ (j, i) = bend) :
      Q.normalSlope j = Q.normalSlope f_bend :=
    (slope_at_bend j i h).trans (slope_at_bend f_bend i_bend vertex_bend).symm
  obtain ⟨links_first, links_last⟩ := regular_forward_links T E P c no_corner
  have regular_of_line {a b : Plane} (different : a ≠ b)
      (agrees : ∀ (t : ℝ) (i : T.Index) (j : Fin 3), AffineMap.lineMap a b t ≠ T.chartCorner E (i, j))
      (w : L.mesh.pairedComplex.Vertex Set.univ) (on_line : Q.projectedVertex w ∈ openSegment ℝ a b) :
      Q.HasRegularSectionSlopes w (b - a) := by
    obtain ⟨t, _, position⟩ := (openSegment_eq_image_lineMap ℝ a b).subset on_line
    exact L.regularSlopes_of_chart_line inside E different agrees w t position
  have reg_first := regular_of_line (fun equal => first_progress.ne
    (congrArg (fun p : Plane => p 0) equal)) links_first
  have reg_last := regular_of_line (fun equal => last_progress.ne
    (congrArg (fun p : Plane => p 0) equal)) links_last
  have g_trace := g_range'.trans g_range
  have flat_of_two (w : L.mesh.pairedComplex.Vertex Set.univ) (a b : Plane)
      (slopes : ∀ j i, L.mesh.pairedComplex.vertexOfCorner Set.univ (j, i) = w →
        Q.normalSlope j = a ∨ Q.normalSlope j = b) :
      L.mesh.pairedComplex.interiorAngularDefect Set.univ w = 0 := by
    have in_segment : Q.incidentSlopes w ⊆ segment ℝ a b := by
      rintro x ⟨j, i, h, rfl⟩
      rcases slopes j i h with equal | equal
      · rw [equal]; exact left_mem_segment ℝ _ _
      · rw [equal]; exact right_mem_segment ℝ _ _
    exact Q.interiorCurvature_eq_zero_of_normalPolygon_collinear w
      ((collinear_segment a b).subset (convexHull_min in_segment (convex_segment a b)))
  have flat_g (w : L.mesh.pairedComplex.Vertex Set.univ)
      (member : Q.projectedVertex w ∈ graphPoint g '' Set.Ioo ((A) 0) ((B) 0)) :
      L.mesh.pairedComplex.interiorAngularDefect Set.univ w = 0 := by
    rw [ConvexRoof.graphPoint_openWindow_eq_twoLinks first_progress last_progress g_trace] at member
    rcases member with (left | right) | middle
    · obtain ⟨p, q, slopes, _⟩ := reg_first w left
      exact flat_of_two w p q slopes
    · obtain ⟨p, q, slopes, _⟩ := reg_last w right
      exact flat_of_two w p q slopes
    · change Q.projectedVertex w = c at middle
      have equality := Q.projectedVertex_injective (middle.trans at_bend.symm)
      subst w
      exact flat_of_two bend (Q.normalSlope f_bend) (Q.normalSlope f_bend)
        (fun j i h => Or.inl (only_bend j i h))
  let cost := sin φ * (2 * φ + tan φ * η) + η
  have closing := Q.abs_sum_graphClosing_errors_le hg first_progress last_progress g_trace
    (fun z hz => contained (Or.inr hz)) sample sample_in endpoints aligned_g reg_first reg_last
    bend at_bend f_bend only_bend nonnegative small (fine_tilt c)
  have same_lift (d : Plane) : Q.sectionDirection f_bend d = K.sectionDirection old_face d := by
    simp only [ConvexRoof.sectionDirection, slope_at_bend f_bend i_bend vertex_bend]
  simp only [same_lift] at closing
  have sine : 0 ≤ sin φ := Real.sin_nonneg_of_nonneg_of_le_pi nonnegative (by linarith only [small, pi_pos])
  have tangent : 0 ≤ tan φ := Real.tan_nonneg_of_nonneg_of_le_pi_div_two nonnegative small.le
  have link_cost :
      sin φ * (2 * φ + tan φ * ‖NormedSpace.normalize (c - (A)) -
        NormedSpace.normalize ((B) - c)‖) ≤ sin φ * (2 * φ + tan φ * η) :=
    mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left mismatch.le tangent)) sine
  have budget := closing.trans (add_le_add link_cost (small_bend old_face).le)
  refine ⟨c, f, sample, hf, f_range, sample_in, ?_⟩
  intro right_bank
  have estimate := Q.abs_graphBankAngleSum_le hf hg ordered start finish contacts
    sample sample_in endpoints aligned_f aligned_g contained flat_g left right first_graph last_graph
    slopes_left slopes_right tangent_left tangent_right
    (by rw [at_left, f_range, g_range']; exact rays_left.mono (fun _ h => h.mp))
    (by rw [at_right, f_range, g_range']; exact rays_right.mono (fun _ h => h.mp))
    nonnegative small (fine_tilt c) (expense := cost) budget right_bank
  exact estimate.trans_eq (by dsimp only [cost]; ring)

end Unfoldings.SpatialEnvelope.FloorMesh
