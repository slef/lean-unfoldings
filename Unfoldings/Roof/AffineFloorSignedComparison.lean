module

public import Unfoldings.Roof.AffineFloorSharpBank
public import Unfoldings.Roof.AffineFloorTerminalBall
public import Unfoldings.Roof.RevisedClosingChart
public import Unfoldings.Roof.HorizontalClosingGraphTrace
public import Unfoldings.Roof.GraphClosingEndpointBalance
public import Unfoldings.Roof.ClosingEndpointSupport
public import Unfoldings.Roof.SignedBankBalance
public import Unfoldings.Geometry.SolidAngleSymmetry

/-! Realize the signed bank comparison on a refinement of the original affine floor mesh. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.FloorMesh

open Filter Topology InnerProductGeometry Real Cap PlanarTopology

universe u

variable {I J : Type u} [Fintype I] [Nonempty I]
  {family : I → SpatialPlane} {floor : Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (T : FloorMesh family floor extra Z)
  (E₀ : Plane ≃ₗᵢ[ℝ] Plane) {n : ℕ} (P₀ : PolygonalChain Plane (n + 1))
  (inside : (interior (clipAbove family floor Z)).Nonempty)

local instance signedCoarseIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

local notation "A₀" => P₀.vertex 0
local notation "B₀" => P₀.vertex (Fin.last (n + 1))
local notation "D₀" => interior (E₀ '' clipAbove family floor Z)
local notation "X" => EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0
local notation "east" => (WithLp.toLp 2 ![(1 : ℝ), 0] : Plane)

/-- The signed slope cell budget is unchanged by reorienting the horizontal chart. -/
theorem solidAngle_gnomonic_image_chart (E : Plane ≃ₗᵢ[ℝ] Plane) {S : Set Plane}
    (compact : IsCompact S) :
    solidAngleMeasure (gnomonicNormal '' (E '' S)) = solidAngleMeasure (gnomonicNormal '' S) := by
  have eq : gnomonicNormal '' (E '' S) = horizontalChartIsometry E '' (gnomonicNormal '' S) := by
    rw [Set.image_image, Set.image_image]
    congr 1
    funext p
    exact (horizontalChartIsometry_gnomonicNormal E p).symm
  rw [eq, solidAngleMeasure_image_of_measurable _ (compact.image gnomonicNormal_lipschitz.continuous).measurableSet]

open Classical in
set_option maxHeartbeats 4200000 in
/-- For every tolerance the actual comparison mesh has one horizontal
closing link and a flat terminal band. It yields the signed angular allowance
on either side of the actual trimmed bank. -/
theorem exists_signed_chartComparison
    (acute : ∀ i, 0 < inner ℝ (B₀ - A₀) (P₀.edge i))
    (in_domain : Set.range P₀.path ⊆ D₀)
    (aligned₀ : ∀ j : T.Index,
      Disjoint (interior (E₀ '' (T.projectedTriangle j).carrier)) (Set.range P₀.path))
    (first₀ : ∀ i, (A₀) ≠ T.chartCorner E₀ i) (last₀ : ∀ i, (B₀) ≠ T.chartCorner E₀ i)
    {cell : Set Plane} (compact : IsCompact cell) (convex_cell : Convex ℝ cell)
    (slopes : ∀ i, (family i).normalSlope ∈ cell)
    {φ D η : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2)
    (tilt : ∀ i, cos φ ≤ (family i).normal 2)
    (pole_area : ∀ p ∈ cell, ∀ q ∈ cell, |orient 0 p q| / 2 ≤ D)
    (tolerance : 0 < η) :
    ∃ (R : Plane ≃ₗᵢ[ℝ] Plane) (c : Plane),
      let E := E₀.trans R
      let P := P₀.reorient R
      let L := chartClosingMesh T E P c inside
      let Q := chartClosingRoof T E P c inside
      (∀ p q : Plane, 0 < orient 0 p q → 0 < orient 0 (R p) (R q)) ∧
      (∀ i, 0 < P.edge i 0) ∧
      ∃ (f : ℝ → ℝ) (sample : L.mesh.Index → Plane), Continuous f ∧
        graphPoint f '' Set.Icc (P.vertex 0 0) (P.vertex (Fin.last (n + 1)) 0) = Set.range P.path ∧
        (∀ j, sample j ∈ interior (Q.projectedTriangle j).carrier) ∧
        ∀ right : Bool, |Q.graphBankAngleSum f sample (P.vertex 0 0) (P.vertex (Fin.last (n + 1)) 0) right| ≤
          2 * arcsin ((1 - cos φ) / (1 + cos φ)) +
            (solidAngleMeasure (gnomonicNormal '' cell)).toReal + D + 4 * η := by
  let K₀ := (T.roof inside).reorient E₀
  let : Finite T.Index := T.finite
  have A_in₀ : (A₀) ∈ D₀ := in_domain (P₀.vertex_mem_path_range 0)
  have B_in₀ : (B₀) ∈ D₀ := in_domain (P₀.vertex_mem_path_range (Fin.last (n + 1)))
  have last_phys (i : T.Index × Fin 3) : E₀.symm (B₀) ≠ (T.projectedTriangle i.1).vertex i.2 := by
    intro eq
    apply last₀ i
    exact ((E₀.apply_symm_apply _).symm.trans (congrArg E₀ eq))
  obtain ⟨r, rp, off_corner, at_coarse⟩ := T.exists_terminalBall_of_off_corners last_phys
  obtain ⟨R, c, oriented, c_in₀, c_ball, progress, first_progress, last_progress, horizontal,
    no_edge₀, no_corner₀, finite, tail, turn, small_bend₀⟩ :=
    K₀.exists_regular_horizontal_shortClosing P₀ (by omega) acute (T.chartCorner E₀)
      (T.chartEdgeEquation E₀) (T.chartEdgeEquation_ne_zero E₀) first₀ last₀
      isOpen_interior A_in₀ B_in₀ rp tolerance
  let E := E₀.trans R
  let P := P₀.reorient R
  let K := (T.roof inside).reorient E
  let A := P.vertex 0
  let B := P.vertex (Fin.last (n + 1))
  let U := interior (E '' clipAbove family floor Z)
  have domain : R '' D₀ = U := by
    change R.toHomeomorph '' interior (E₀ '' clipAbove family floor Z) = _
    rw [R.toHomeomorph.image_interior, Set.image_image]
    rfl
  have in_path : Set.range P.path ⊆ U := by
    rw [← domain, P₀.path_range_reorient]
    exact Set.image_mono in_domain
  have A_in : A ∈ U := in_path (P.vertex_mem_path_range 0)
  have B_in : B ∈ U := in_path (P.vertex_mem_path_range (Fin.last (n + 1)))
  have c_in : c ∈ U := domain ▸ c_in₀
  have alignment (j : T.Index) :
      Disjoint (interior (E '' (T.projectedTriangle j).carrier)) (Set.range P.path) := by
    rw [show E '' (T.projectedTriangle j).carrier = R '' (E₀ '' (T.projectedTriangle j).carrier)
      by rw [Set.image_image]; rfl, P₀.path_range_reorient]
    change Disjoint (interior (R.toHomeomorph '' (E₀ '' (T.projectedTriangle j).carrier))) _
    rw [← R.toHomeomorph.image_interior]
    exact (aligned₀ j).image R.injective.injOn (Set.subset_univ _) (Set.subset_univ _)
  have first (i : T.Index × Fin 3) : A ≠ T.chartCorner E i :=
    R.injective.ne (first₀ i)
  have last (i : T.Index × Fin 3) : B ≠ T.chartCorner E i :=
    R.injective.ne (last₀ i)
  have no_corner (j : Fin 2) (t : ℝ) (i : T.Index × Fin 3) :
      AffineMap.lineMap (P.twoClosingLinks c j).1 (P.twoClosingLinks c j).2 t ≠ T.chartCorner E i :=
    no_corner₀ j t i
  have no_edge (i : T.Index × Fin 3) : T.chartEdgeEquation E i c ≠ 0 := by
    let p := T.chartCorner E₀ i
    let q := T.chartCorner E₀ (i.1, Triangle.next i.2)
    have ne : p ≠ q := E₀.injective.ne ((T.projectedTriangle i.1).edge_endpoints_ne i.2)
    have original : orient p q (R.symm c) ≠ 0 := by
      have h : segmentEquation p q (R.symm c) ≠ 0 := no_edge₀ i
      rwa [segmentEquation, ite_eq_right ne, orientMap_apply] at h
    have nonzero := orient_map_ne_zero R.toAffineIsometryEquiv original
    change orient (R p) (R q) (R (R.symm c)) ≠ 0 at nonzero
    rw [R.apply_symm_apply] at nonzero
    change segmentEquation (R p) (R q) c ≠ 0
    rwa [segmentEquation, ite_eq_right (R.injective.ne ne), orientMap_apply]
  have convex : Convex ℝ U :=
    ((convex_clipAbove family floor Z).linear_image E.toLinearEquiv.toLinearMap).interior
  let G := P.forwardClosingChain c
  have progress_g := P.forwardClosingChain_progress c first_progress last_progress
  have ordered := first_progress.trans last_progress
  have skeleton := T.chart_aligned_subset_skeleton E P in_path alignment
  have g_range : Set.range G.path = segment ℝ (A) c ∪ segment ℝ c (B) := by
    rw [P.forwardClosingChain_trace c, segment_symm ℝ (B) c, segment_symm ℝ c (A), Set.union_comm]
  have G_in : Set.range G.path ⊆ U := by
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
  let L := chartClosingMesh T E P c inside
  let : Fintype L.mesh.Index := @Fintype.ofFinite _ L.mesh.finite
  let Q := chartClosingRoof T E P c inside
  have footprint : Q.footprint = E '' clipAbove family floor Z :=
    chartClosingRoof_footprint T E P c inside
  have contained :
      (graphPoint f '' Set.Icc ((A) 0) ((B) 0)) ∪
        (graphPoint g '' Set.Icc ((A) 0) ((B) 0)) ⊆ interior Q.footprint := by
    rw [f_range, g_range', footprint]
    exact Set.union_subset in_path G_in
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
  have mark (i : Fin 4) (h : closingMark P c i ∈ U) :
      ∃ w : L.mesh.pairedComplex.Vertex Set.univ, Q.projectedVertex w = closingMark P c i :=
    exists_chartClosingRoof_markedVertex T E P c inside i (footprint.symm ▸ interior_subset h)
  obtain ⟨left, at_left⟩ := mark 0 A_in
  obtain ⟨right, at_right⟩ := mark 1 B_in
  obtain ⟨bend, at_bend⟩ := mark 2 c_in
  have mid_in := convex.midpoint_mem A_in c_in
  obtain ⟨middle, at_middle⟩ := mark 3 mid_in
  have on_middle : Q.projectedVertex middle ∈ openSegment ℝ A c := by
    change Q.projectedVertex middle = midpoint ℝ A c at at_middle
    rw [at_middle]
    exact midpoint_mem_openSegment (𝕜 := ℝ) A c
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
  have rays_left := P.eventually_mem_union_forwardChains_iff_initial_rays G (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0)
    progress progress_g rfl
  have rays_right := P.eventually_mem_union_forwardChains_iff_terminal_rays G (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0)
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
  have phys_ball {x : Plane} (h : x ∈ Metric.ball B r) : E.symm x ∈ Metric.ball (E₀.symm (B₀)) r := by
    have eq : E.symm B = E₀.symm (B₀) := by
      change E₀.symm (R.symm (R (B₀))) = _
      rw [R.symm_apply_apply]
    rw [← eq]
    simpa only [Metric.mem_ball, E.symm.dist_map] using h
  have last_coarse := at_coarse (E.symm c) (phys_ball c_ball) old_face (interior_subset old_interior)
  have short_interior {x : Plane} (hx : x ∈ segment ℝ c B) (ne : x ≠ B) :
      E.symm x ∈ interior (T.projectedTriangle old_face).carrier := by
    rw [segment_symm] at hx
    obtain ⟨t, ht, equal⟩ := (segment_eq_image_lineMap ℝ B c).subset hx
    have tp : 0 < t := lt_of_le_of_ne ht.1 (by
      intro zero
      apply ne
      rw [← equal, ← zero, AffineMap.lineMap_apply_zero])
    rw [← equal, ← PolygonalChain.lineMap_reorient]
    rw [AffineMap.lineMap_apply_module', add_comm]
    change E.symm B + t • (E.symm c - E.symm B) ∈ _
    have b_mem : E.symm B ∈ (T.projectedTriangle old_face).carrier := by
      change E₀.symm (R.symm (R (B₀))) ∈ _
      rw [R.symm_apply_apply]
      exact last_coarse
    exact (T.projectedTriangle old_face).convex_carrier.add_smul_sub_mem_interior b_mem old_interior ⟨tp, ht.2⟩
  have flat_short (w : L.mesh.pairedComplex.Vertex Set.univ) (on : Q.projectedVertex w ∈ segment ℝ c B)
      (ne : Q.projectedVertex w ≠ B) (j : L.mesh.Index) (i : Fin 3)
      (h : L.mesh.pairedComplex.vertexOfCorner Set.univ (j, i) = w) :
      Q.normalSlope j = Q.normalSlope f_bend :=
    (L.chart_slope_eq_of_mem_original_interior inside E w old_face (by
      have hit := short_interior on ne
      change E.symm (((L.mesh.roof inside).reorient E).projectedVertex w) ∈ _ at hit
      rwa [ConvexRoof.projectedVertex_reorient, E.symm_apply_apply] at hit) j i h).trans (slope_at_bend f_bend i_bend vertex_bend).symm
  obtain ⟨links_first, _⟩ := regular_forward_links T E P c no_corner
  have reg_first (w : L.mesh.pairedComplex.Vertex Set.univ) (on_line : Q.projectedVertex w ∈ openSegment ℝ A c) :
      Q.HasRegularSectionSlopes w (c - A) := by
    obtain ⟨t, _, position⟩ := (openSegment_eq_image_lineMap ℝ A c).subset on_line
    exact L.regularSlopes_of_chart_line inside E
      (fun equal => first_progress.ne (congrArg (fun p : Plane => p 0) equal)) links_first w t position
  have coords := g_range'.trans g_range
  have flat_of_two (w : L.mesh.pairedComplex.Vertex Set.univ) (a b : Plane)
      (hs : ∀ j i, L.mesh.pairedComplex.vertexOfCorner Set.univ (j, i) = w →
        Q.normalSlope j = a ∨ Q.normalSlope j = b) :
      L.mesh.pairedComplex.interiorAngularDefect Set.univ w = 0 := by
    have in_segment : Q.incidentSlopes w ⊆ segment ℝ a b := by
      rintro x ⟨j, i, h, rfl⟩
      rcases hs j i h with equal | equal
      · rw [equal]; exact left_mem_segment ℝ _ _
      · rw [equal]; exact right_mem_segment ℝ _ _
    exact Q.interiorCurvature_eq_zero_of_normalPolygon_collinear w
      ((collinear_segment a b).subset (convexHull_min in_segment (convex_segment a b)))
  have flat_g (w : L.mesh.pairedComplex.Vertex Set.univ)
      (member : Q.projectedVertex w ∈ graphPoint g '' Set.Ioo (A 0) (B 0)) :
      L.mesh.pairedComplex.interiorAngularDefect Set.univ w = 0 := by
    rw [ConvexRoof.graphPoint_openWindow_eq_twoLinks first_progress last_progress coords] at member
    rcases member with (early | late) | middle
    · obtain ⟨p, q, hs, _⟩ := reg_first w early
      exact flat_of_two w p q hs
    · have ne : Q.projectedVertex w ≠ B := fun h =>
        (ConvexRoof.horizontal_mem_Ioo_of_mem_openSegment last_progress late).2.ne (congrArg (fun x : Plane => x 0) h)
      exact flat_of_two w (Q.normalSlope f_bend) (Q.normalSlope f_bend)
        (fun j i h => Or.inl (flat_short w (openSegment_subset_segment ℝ _ _ late) ne j i h))
    · change Q.projectedVertex w = c at middle
      have eq := Q.projectedVertex_injective (middle.trans at_bend.symm)
      subst w
      exact flat_of_two bend (Q.normalSlope f_bend) (Q.normalSlope f_bend) (fun j i h => Or.inl (only_bend j i h))
  have flat_tail (w : L.mesh.pairedComplex.Vertex Set.univ) (late : c 0 < Q.projectedVertex w 0)
      (window : Q.projectedVertex w 0 ∈ Set.Ioo (A 0) (B 0))
      (band : Q.projectedVertex w 1 ∈ Set.uIcc (f (Q.projectedVertex w 0)) (g (Q.projectedVertex w 0))) :
      L.mesh.pairedComplex.interiorAngularDefect Set.univ w = 0 := by
    let x := Q.projectedVertex w 0
    have f_ball : graphPoint f x ∈ Metric.ball B r :=
      tail _ (f_range.subset (Set.mem_image_of_mem _ (Set.Ioo_subset_Icc_self window))) late.le
    have g_ball : graphPoint g x ∈ Metric.ball B r := by
      have on := coords.subset (Set.mem_image_of_mem (graphPoint g) (Set.Ioo_subset_Icc_self window))
      rcases on with early | close
      · exact (late.not_ge (ConvexRoof.horizontal_mem_Icc_of_mem_segment first_progress.le early).2).elim
      · exact (convex_ball B r).segment_subset c_ball (Metric.mem_ball_self rp) close
    let v : ℝ →ᵃ[ℝ] Plane := AffineMap.const ℝ ℝ (graphPoint (fun _ => 0) x) +
      (LinearMap.toSpanSingleton ℝ Plane (WithLp.toLp 2 ![0, 1])).toAffineMap
    have form (y : ℝ) : v y = WithLp.toLp 2 ![x, y] := by
      apply PiLp.ext
      intro i
      fin_cases i <;> simp [v, graphPoint, LinearMap.toSpanSingleton_apply]
    have segment_mem : Q.projectedVertex w ∈ segment ℝ (graphPoint f x) (graphPoint g x) := by
      rw [← show v (f x) = graphPoint f x from form _, ← show v (g x) = graphPoint g x from form _,
        ← image_segment ℝ v, segment_eq_uIcc]
      refine ⟨Q.projectedVertex w 1, band, (form _).trans ?_⟩
      apply PiLp.ext
      intro i
      fin_cases i <;> rfl
    have ball := phys_ball ((convex_ball B r).segment_subset f_ball g_ball segment_mem)
    apply L.zeroCurvature_of_off_chartCorners inside E w
    intro i h
    have eq : Q.projectedVertex w = T.chartCorner E i := h
    exact off_corner _ ball i (by rw [eq]; exact E.symm_apply_apply _)
  let S := E '' cell
  have fine_slopes (j : L.mesh.Index) : Q.normalSlope j ∈ S := by
    change ((L.mesh.roof inside).reorient E).normalSlope j ∈ _
    rw [ConvexRoof.normalSlope_reorient, L.roof_normalSlope inside]
    exact Set.mem_image_of_mem E (slopes _)
  have fine_tilt : Q.TiltBound φ := fun j => tilt (L.mesh.support j)
  obtain ⟨m, trace, init, t, tp, init_start, init_finish, trace_start, trace_end, closing⟩ :=
    Q.exists_horizontalClosingGraph_trace hg first_progress last_progress horizontal coords
      (fun p hp => contained (Or.inr hp)) sample sample_in endpoints aligned_g reg_first
      left bend middle at_left at_bend on_middle f_bend flat_short nonnegative small fine_tilt fine_slopes
  have long_eq : c - A = (c 0 - A 0) • east := by
    ext i
    fin_cases i
    · change c 0 - A 0 = (c 0 - A 0) * 1
      rw [mul_one]
    · change c 1 - A 1 = (c 0 - A 0) * 0
      rw [horizontal, sub_self, mul_zero]
  have init_corner :
      L.mesh.pairedComplex.vertexOfCorner Set.univ (init.1.1, (L.mesh.pairedComplex.germFarCorner init).2) = left := by
    apply Q.projectedVertex_injective
    rw [Q.projectedVertex_ofCorner, at_left]
    exact init_finish
  have init_hit : A ∈ (Q.projectedTriangle init.1.1).carrier := by
    rw [← show Q.projectedGermFinish init = A from init_finish]
    exact (Q.projectedTriangle init.1.1).vertex_mem _
  have init_ray : A + (t / (c 0 - A 0)) • (c - A) ∈ (Q.projectedTriangle init.1.1).carrier := by
    rw [long_eq, smul_smul, div_mul_cancel₀ _ (sub_pos.mpr first_progress).ne', ←
      show Q.projectedGermStart init = A + t • east from init_start]
    exact (Q.projectedTriangle init.1.1).vertex_mem _
  have active_left (i : L.mesh.Index) (z : ℝ) (zp : 0 < z)
      (transverse : orient 0 (P.edge 0) (c - A) ≠ 0)
      (corner : ∃ k, L.mesh.pairedComplex.vertexOfCorner Set.univ (i, k) = left)
      (base : Q.projectedVertex left ∈ (Q.projectedTriangle i).carrier)
      (ray : Q.projectedVertex left + z • (c - A) ∈ (Q.projectedTriangle i).carrier) :
      Q.normalSlope i = Q.normalSlope init.1.1 := by
    obtain ⟨k, named⟩ := corner
    rw [at_left] at base ray
    exact Q.normalSlope_eq_of_shared_endpoint_ray i init.1.1 transverse tangent_left
      (slopes_left i k named) (slopes_left _ _ init_corner) base init_hit zp
      (div_pos tp (sub_pos.mpr first_progress)) ray init_ray
  have active_right (i : L.mesh.Index) (z : ℝ) (zp : 0 < z)
      (_ : orient 0 (-P.edge (Fin.last n)) (c - B) ≠ 0)
      (_ : ∃ k, L.mesh.pairedComplex.vertexOfCorner Set.univ (i, k) = right)
      (base : Q.projectedVertex right ∈ (Q.projectedTriangle i).carrier)
      (ray : Q.projectedVertex right + z • (c - B) ∈ (Q.projectedTriangle i).carrier) :
      Q.normalSlope i = Q.normalSlope f_bend := by
    rw [at_right] at base ray
    let ε := min z 1
    have ep : 0 < ε := lt_min zp zero_lt_one
    let x := B + ε • (c - B)
    have x_fine : x ∈ (Q.projectedTriangle i).carrier := by
      apply (Q.projectedTriangle i).convex_carrier.segment_subset base ray
      rw [← show AffineMap.lineMap B (B + z • (c - B)) (ε / z) = x by
        rw [AffineMap.lineMap_apply_module', add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ zp.ne', add_comm]]
      exact lineMap_mem_segment ℝ _ _ ⟨div_nonneg ep.le zp.le, (div_le_one zp).mpr (min_le_left _ _)⟩
    have x_close : x ∈ segment ℝ c B := by
      rw [segment_symm, ← show AffineMap.lineMap B c ε = x by rw [AffineMap.lineMap_apply_module', add_comm]]
      exact lineMap_mem_segment ℝ _ _ ⟨ep.le, min_le_right _ _⟩
    have x_ne : x ≠ B := by
      intro eq
      have coord := congrArg (fun p : Plane => p 0) eq
      change B 0 + ε * (c 0 - B 0) = B 0 at coord
      linarith only [coord, mul_neg_of_pos_of_neg ep (sub_neg.mpr last_progress)]
    exact (L.chart_slope_eq_of_point_mem_coarse_interior inside E old_face i
      (short_interior x_close x_ne) x_fine).trans (slope_at_bend f_bend i_bend vertex_bend).symm
  have bank_segment (j : Fin (n + 1)) :
      segment ℝ (P.vertex j.castSucc) (P.vertex j.succ) ⊆ Set.range P.path := by
    rw [P.path_range_eq_segments]
    intro z hz
    exact Or.inr (Set.mem_iUnion.mpr ⟨j, hz⟩)
  have left_bank : segment ℝ A (A + P.edge 0) ⊆ graphPoint f '' Set.Icc (A 0) (B 0) := by
    rw [f_range, PolygonalChain.edge]
    change segment ℝ (P.vertex (0 : Fin (n + 1)).castSucc)
      (P.vertex (0 : Fin (n + 1)).castSucc + (P.vertex (0 : Fin (n + 1)).succ -
        P.vertex (0 : Fin (n + 1)).castSucc)) ⊆ _
    convert bank_segment (0 : Fin (n + 1)) using 2
    abel
  have right_bank : segment ℝ B (B + -P.edge (Fin.last n)) ⊆ graphPoint f '' Set.Icc (A 0) (B 0) := by
    rw [f_range, PolygonalChain.edge, neg_sub, show (Fin.last n).succ = Fin.last (n + 1) from Fin.succ_last n]
    change segment ℝ B (B + (P.vertex (Fin.last n).castSucc - B)) ⊆ _
    rw [segment_symm]
    convert bank_segment (Fin.last n) using 2 <;> simp [B, Fin.succ_last]
  have left_close : segment ℝ A (A + (c - A)) ⊆ graphPoint g '' Set.Icc (A 0) (B 0) := by
    rw [show A + (c - A) = c by abel, coords]
    exact Set.subset_union_left
  have right_close : segment ℝ B (B + (c - B)) ⊆ graphPoint g '' Set.Icc (A 0) (B 0) := by
    rw [show B + (c - B) = c by abel, segment_symm, coords]
    exact Set.subset_union_right
  have left_error := Q.graphEndpoint_excess_sub_eq_headingError hf hg ordered start finish contacts
    sample sample_in aligned_f aligned_g contained true left first_graph
    (u := P.edge 0) (v := c - A) (progress 0) (sub_pos.mpr first_progress)
    (by simpa only [at_left] using left_bank) (by simpa only [at_left] using left_close)
    slopes_left tangent_left (by
      rw [at_left, f_range, g_range']
      exact rays_left.mono (fun _ h => h.mp)) init.1.1 active_left
  have right_error := Q.graphEndpoint_excess_sub_eq_headingError hf hg ordered start finish contacts
    sample sample_in aligned_f aligned_g contained false right last_graph
    (u := -P.edge (Fin.last n)) (v := c - B) (by change 0 < -(-P.edge (Fin.last n) 0); rw [neg_neg]; exact progress _)
    (by change 0 < -(c 0 - B 0); linarith only [last_progress])
    (by simpa only [at_right] using right_bank) (by simpa only [at_right] using right_close)
    slopes_right tangent_right (by
      rw [at_right, f_range, g_range']
      have dir : -G.edge (Fin.last 1) = c - B := by
        change -(B - c) = c - B
        rw [neg_sub]
      exact rays_right.mono (fun _ h hit => by simpa only [dir] using h.mp hit)) f_bend active_right
  simp only [ite_true, one_mul] at left_error
  simp only [Bool.false_eq_true, ite_false, neg_one_mul] at right_error
  have same_section (d : Plane) : Q.sectionDirection f_bend d =
      (K₀.reorient R).sectionDirection old_face d := by
    have normal : K.normalSlope old_face = (K₀.reorient R).normalSlope old_face := by
      dsimp only [K, K₀]
      rw [ConvexRoof.normalSlope_reorient, ConvexRoof.normalSlope_reorient, ConvexRoof.normalSlope_reorient]
      rfl
    simp only [ConvexRoof.sectionDirection, slope_at_bend f_bend i_bend vertex_bend, normal]
  have bend_cost : |angle (Q.sectionDirection f_bend (c - A)) (Q.sectionDirection f_bend (B - c)) -
      angle (c - A) (B - c)| < η := by
    rw [same_section, same_section]
    exact small_bend₀ old_face
  have cA_ne : c - A ≠ 0 := sub_ne_zero.mpr
    (fun h => first_progress.ne (congrArg (fun p : Plane => p 0) h.symm))
  have Bc_ne : B - c ≠ 0 := sub_ne_zero.mpr
    (fun h => last_progress.ne (congrArg (fun p : Plane => p 0) h.symm))
  have bank_left_ne : P.edge 0 ≠ 0 := fun h => (progress 0).ne' (by rw [h]; rfl)
  have bank_right_ne : -P.edge (Fin.last n) ≠ 0 :=
    neg_ne_zero.mpr (fun h => (progress (Fin.last n)).ne' (by rw [h]; rfl))
  have short_heading := Q.abs_sectionHeadingError_sub_le f_bend cA_ne Bc_ne
  have spatial_cost : angle (Q.sectionDirection f_bend (c - A)) (Q.sectionDirection f_bend (B - c)) <
      2 * η := by linarith only [(le_abs_self _).trans_lt bend_cost, turn]
  have near_heading : |Q.sectionHeadingError f_bend (B - c) - Q.sectionHeadingError f_bend (c - A)| ≤ 3 * η :=
    short_heading.trans (by linarith only [spatial_cost, turn])
  have sections (j : L.mesh.Index) : Q.sectionHeadingError j (c - A) =
      radialSectionHeading (Q.normalSlope j 0) (Q.normalSlope j 1) := by
    rw [long_eq, Q.sectionHeadingError_smul_of_pos j (sub_pos.mpr first_progress), Q.sectionHeadingError_east]
  have cos_pos := cos_pos_of_mem_Ioo (show φ ∈ Set.Ioo (-(π / 2)) (π / 2) from
    ⟨(neg_lt_zero.mpr (half_pos pi_pos)).trans_le nonnegative, small⟩)
  have left_budget := Q.abs_sectionHeadingError_le init.1.1 cos_pos (fine_tilt _) bank_left_ne
  have right_budget := Q.abs_sectionHeadingError_le f_bend cos_pos (fine_tilt _) bank_right_ne
  let F := Q.regionalAngleExcess (ConvexRoof.facesAboveGraph sample f (A 0) (B 0))
  let H := Q.regionalAngleExcess (ConvexRoof.facesAboveGraph sample g (A 0) (B 0))
  let p := trace.path.vertex 0
  let q := trace.path.vertex (Fin.last (m + 1))
  have end_charge : |(F left - H left) + (F right - H right) +
      (radialSectionHeading (q 0) (q 1) - radialSectionHeading (p 0) (p 1))| ≤
        2 * arcsin ((1 - cos φ) / (1 + cos φ)) + 3 * η := by
    change F left - H left = _ at left_error
    change F right - H right = _ at right_error
    rw [left_error, right_error, show p = _ from trace_start, show q = _ from trace_end,
      ← sections init.1.1, ← sections f_bend, ← neg_sub B c, Q.sectionHeadingError_neg]
    have eq :
        Q.sectionHeadingError init.1.1 (c - A) - Q.sectionHeadingError init.1.1 (P.edge 0) +
          -(Q.sectionHeadingError f_bend (B - c) - Q.sectionHeadingError f_bend (-P.edge (Fin.last n))) +
          (Q.sectionHeadingError f_bend (c - A) - Q.sectionHeadingError init.1.1 (c - A)) =
        (-Q.sectionHeadingError init.1.1 (P.edge 0) + Q.sectionHeadingError f_bend (-P.edge (Fin.last n))) +
          -(Q.sectionHeadingError f_bend (B - c) - Q.sectionHeadingError f_bend (c - A)) := by ring
    rw [eq]
    refine (abs_add_le _ _).trans ?_
    have endpoint := abs_add_le (-Q.sectionHeadingError init.1.1 (P.edge 0))
      (Q.sectionHeadingError f_bend (-P.edge (Fin.last n)))
    simp only [abs_neg] at endpoint ⊢
    linarith only [endpoint, left_budget, right_budget, near_heading]
  have solid : solidAngleMeasure (gnomonicNormal '' S) = solidAngleMeasure (gnomonicNormal '' cell) :=
    solidAngle_gnomonic_image_chart E compact
  have det : |p 0 * q 1 - q 0 * p 1| / 2 ≤ D := by
    obtain ⟨a, ha, pa⟩ := trace.inside 0
    obtain ⟨b, hb, qb⟩ := trace.inside (Fin.last (m + 1))
    have to_area : p 0 * q 1 - q 0 * p 1 = orient 0 p q := by
      simp only [orient, PiLp.zero_apply, sub_zero]
      ring
    rw [to_area, ← show E a = p from pa, ← show E b = q from qb, abs_orient_linearIsometryEquiv]
    exact pole_area a ha b hb
  refine ⟨R, c, oriented, progress, f, sample, hf, f_range, sample_in, ?_⟩
  intro right_bank
  have estimate := Q.abs_graphBankAngleSum_le_signed hf hg ordered start finish contacts
    sample sample_in endpoints aligned_f aligned_g contained flat_g left right first_graph last_graph
    (cutoff := c 0) (fun _ window early =>
      ConvexRoof.graphClosing_value_of_before_bend first_progress last_progress horizontal coords
        (Set.Ioo_subset_Icc_self window) early) flat_tail
    (compact.image E.continuous) (convex_cell.linear_image E.toLinearEquiv.toLinearMap) fine_slopes
    trace (closing.trans bend_cost.le) end_charge right_bank
  change |Q.graphBankAngleSum f sample (A 0) (B 0) right_bank| ≤
    (solidAngleMeasure (gnomonicNormal '' S)).toReal + |p 0 * q 1 - q 0 * p 1| / 2 +
       (η + (2 * arcsin ((1 - cos φ) / (1 + cos φ)) + 3 * η)) at estimate
  rw [solid] at estimate
  linarith only [estimate, det]

end Unfoldings.SpatialEnvelope.FloorMesh
