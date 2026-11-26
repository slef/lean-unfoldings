module

public import Unfoldings.Roof.ActiveNormalTrace
public import Unfoldings.Roof.ClosingNormalCurvature
public import Unfoldings.Geometry.GnomonicTriangleTransport

/-! A polygonal sequence of actual supported slope changes on a horizontal link. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Real Cap MeasureTheory PlanarTopology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}

structure SupportedNormalTrace (K : ConvexRoof C) (cell : Set Plane) (level : ℝ) (n : ℕ) where
  path : PolygonalChain Plane n
  advancing : ∀ i, 0 ≤ (path.edge i) 0
  flat : ∀ i, (path.edge i) 0 = 0 → path.edge i = 0
  inside : ∀ i, path.vertex i ∈ cell
  contact : Fin n → Plane
  on_line : ∀ i, (contact i) 1 = level
  left_support : ∀ i, path.vertex i.castSucc ∈ supportingSlopes K.roofHeight (contact i)
  right_support : ∀ i, path.vertex i.succ ∈ supportingSlopes K.roofHeight (contact i)
  slope : Fin n → ℝ
  intercept : Fin n → ℝ
  left_normal_line : ∀ i, path.vertex i.castSucc 1 = slope i * path.vertex i.castSucc 0 + intercept i
  right_normal_line : ∀ i, path.vertex i.succ 1 = slope i * path.vertex i.succ 0 + intercept i

namespace SupportedNormalTrace

variable {K : ConvexRoof C} {cell : Set Plane} {level : ℝ} {n : ℕ}
  (T : K.SupportedNormalTrace cell level n)

/-- The exact real turn of the sequence in its horizontal-axis frame. -/
def hingeSum : ℝ := ∑ i, hingeAngleChange (T.slope i) (T.intercept i)
  (T.path.vertex i.castSucc 0) (T.path.vertex i.succ 0)

private theorem graphPoint_affine_mem_segment {p q : Plane} {m b t : ℝ}
    (left : p 1 = m * p 0 + b) (right : q 1 = m * q 0 + b) (within : t ∈ Set.uIcc (p 0) (q 0)) :
    graphPoint (fun u => m * u + b) t ∈ segment ℝ p q := by
  let f : ℝ →ᵃ[ℝ] Plane := AffineMap.const ℝ ℝ (WithLp.toLp 2 ![0, b]) +
    (LinearMap.toSpanSingleton ℝ Plane (WithLp.toLp 2 ![1, m])).toAffineMap
  have form (x : ℝ) : f x = graphPoint (fun u => m * u + b) x := by
    ext j
    fin_cases j
    · change 0 + x * 1 = x
      ring
    · change b + x * m = m * x + b
      ring
  have eq (x : Plane) (on_line : x 1 = m * x 0 + b) : f (x 0) = x := by
    rw [form]
    ext j
    fin_cases j
    · rfl
    · exact on_line.symm
  rw [← form, ← eq p left, ← eq q right, ← image_segment ℝ f, segment_eq_uIcc]
  exact Set.mem_image_of_mem f within

private theorem continuity_of_trace (positive : 0 < n) (convex : Convex ℝ cell) :
    ∃ trace : ℝ → ℝ, Continuous trace ∧
      (∀ i, trace (T.path.vertex i 0) = T.path.vertex i 1) ∧
      (∀ t ∈ Set.Icc (T.path.vertex 0 0) (T.path.vertex (Fin.last n) 0),
        graphPoint trace t ∈ cell ∧ ∃ x : Plane, x 1 = level ∧
          graphPoint trace t ∈ supportingSlopes K.roofHeight x) ∧
      ∀ i : Fin n, ∀ t ∈ Set.Icc (T.path.vertex i.castSucc 0) (T.path.vertex i.succ 0),
        trace t = T.slope i * t + T.intercept i := by
  obtain ⟨trace, continuous, vertex, graph⟩ :=
    T.path.exists_continuous_graph_of_weak_horizontal positive T.advancing T.flat
  refine ⟨trace, continuous, vertex, ?_, ?_⟩
  · intro t at_t
    have member : graphPoint trace t ∈ Set.range T.path.path := graph ▸ ⟨t, at_t, rfl⟩
    rw [T.path.path_range_eq_segments] at member
    rcases member with first | rest
    · have eq : graphPoint trace t = T.path.vertex 0 := first
      let j : Fin n := ⟨0, positive⟩
      exact ⟨eq.symm ▸ T.inside 0, T.contact j, T.on_line j, eq.symm ▸ T.left_support j⟩
    · obtain ⟨j, member⟩ := Set.mem_iUnion.mp rest
      exact ⟨convex.segment_subset (T.inside j.castSucc) (T.inside j.succ) member,
        T.contact j, T.on_line j,
        (convex_supportingSlopes K.roofHeight _).segment_subset
          (T.left_support j) (T.right_support j) member⟩
  · intro j t ht
    have at_t := graphPoint_affine_mem_segment (T.left_normal_line j) (T.right_normal_line j)
      (show t ∈ Set.uIcc (T.path.vertex j.castSucc 0) (T.path.vertex j.succ 0) from
        Set.Icc_subset_uIcc ht)
    have trace_mem : graphPoint (fun x => T.slope j * x + T.intercept j) t ∈ Set.range T.path.path := by
      rw [T.path.path_range_eq_segments]
      right
      exact Set.mem_iUnion.mpr ⟨j, at_t⟩
    obtain ⟨x, _, he⟩ := graph.symm.subset trace_mem
    have h : x = t := congrArg (fun p : Plane => p 0) he
    subst x
    exact congrArg (fun p : Plane => p 1) he


private theorem hingeSum_eq_transport {trace : ℝ → ℝ} (continuous : Continuous trace)
    (affine : ∀ i : Fin n, ∀ t ∈ Set.Icc (T.path.vertex i.castSucc 0) (T.path.vertex i.succ 0),
      trace t = T.slope i * t + T.intercept i)
    (m b : ℝ) :
    let p := T.path.vertex 0 0
    let q := T.path.vertex (Fin.last n) 0
    hingeAngleChange m b p q - T.hingeSum =
      ∫ z, normalRibbonWinding trace (fun t => m * t + b) p q z ∂Cap.cartesianSolidAngle := by
  let V (k : ℕ) : Fin (n + 1) := ⟨min k n, Nat.lt_succ_of_le (min_le_right _ _)⟩
  let X (k : ℕ) := T.path.vertex (V k) 0
  let M (k : ℕ) := if h : k < n then T.slope ⟨k, h⟩ else 0
  let B (k : ℕ) := if h : k < n then T.intercept ⟨k, h⟩ else 0
  have at_i (i : Fin (n + 1)) : V i.val = i :=
    Fin.ext (min_eq_left (Nat.le_of_lt_succ i.isLt))
  have at_n : V n = Fin.last n := at_i (Fin.last n)
  have at_zero : V 0 = 0 := at_i 0
  let x := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0
  have ordered : Monotone (fun i => x (T.path.vertex i)) :=
    (T.path.monotone_linear_vertices_iff x).mpr T.advancing
  have inc : Monotone X := fun a b h => ordered (show V a ≤ V b from min_le_min_right _ h)
  have pieces (i : ℕ) (hi : i < n) (t : ℝ) (ht : t ∈ Set.Icc (X i) (X (i + 1))) :
      trace t = M i * t + B i := by
    let j : Fin n := ⟨i, hi⟩
    change t ∈ Set.Icc (T.path.vertex (V j.castSucc.val) 0)
      (T.path.vertex (V j.succ.val) 0) at ht
    rw [at_i, at_i] at ht
    simpa only [M, B, dite_eq_left hi] using affine j t ht
  have exact_sum :
      (∑ i ∈ Finset.range n, hingeAngleChange (M i) (B i) (X i) (X (i + 1))) = T.hingeSum := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    change hingeAngleChange (M j.val) (B j.val) (T.path.vertex (V j.castSucc.val) 0)
      (T.path.vertex (V j.succ.val) 0) = _
    rw [at_i, at_i]
    simp only [M, B, dite_eq_left j.isLt]
  have h := hingeChord_sub_trace_eq_winding continuous X M B inc pieces m b
  rw [exact_sum] at h
  change hingeAngleChange m b (T.path.vertex (V 0) 0) (T.path.vertex (V n) 0) - T.hingeSum =
    (∫ z, normalRibbonWinding trace (fun t => m * t + b)
      (T.path.vertex (V 0) 0) (T.path.vertex (V n) 0) z ∂Cap.cartesianSolidAngle) at h
  rwa [at_zero, at_n] at h

/-- The signed normal transport and intrinsic curvature cost one cell solid
angle plus the planar area of the pole triangle. -/
theorem abs_signed_defects_add_hingeSum_sub_radial_le (positive : 0 < n)
    (compact : IsCompact cell) (convex : Convex ℝ cell) (slopes : ∀ f, K.normalSlope f ∈ cell)
    (weight : C.Vertex Set.univ → ℝ) (bounded : ∀ v, |weight v| ≤ 1)
    (sign : ∀ v, 0 ≤ (K.projectedVertex v 1 - level) * weight v)
    (on_link : ∀ v, K.projectedVertex v 1 = level → weight v = 0) :
    let p := T.path.vertex 0
    let q := T.path.vertex (Fin.last n)
    |(∑ v, weight v * C.interiorAngularDefect Set.univ v) + T.hingeSum -
      (radialSectionHeading (q 0) (q 1) - radialSectionHeading (p 0) (p 1))| ≤
      (solidAngleMeasure (gnomonicNormal '' cell)).toReal + |p 0 * q 1 - q 0 * p 1| / 2 := by
  obtain ⟨trace, continuous, vertex, support, affine⟩ := T.continuity_of_trace positive convex
  let p := T.path.vertex 0
  let q := T.path.vertex (Fin.last n)
  let x := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0
  have ordered : Monotone (fun i => x (T.path.vertex i)) :=
    (T.path.monotone_linear_vertices_iff x).mpr T.advancing
  have pq : p 0 ≤ q 0 := ordered (Fin.zero_le _)
  have u (t : ℝ) (within : t ∈ Set.Ioc (p 0) (q 0)) :
      ∃ point : Plane, point 1 = level ∧ graphPoint trace t ∈ supportingSlopes K.roofHeight point :=
    (support t (Set.Ioc_subset_Icc_self within)).2
  have mem_trace (t : ℝ) (within : t ∈ Set.Ioc (p 0) (q 0)) : graphPoint trace t ∈ cell :=
    (support t (Set.Ioc_subset_Icc_self within)).1
  by_cases lt : p 0 < q 0
  · let m := (q 1 - p 1) / (q 0 - p 0)
    let b := p 1 - m * p 0
    let chord (t : ℝ) := m * t + b
    have p_line : m * p 0 + b = p 1 := by dsimp [b]; ring
    have q_line : m * q 0 + b = q 1 := by
      dsimp only [b, m]
      field_simp [(sub_pos.mpr lt).ne']
      ring
    have mem_chord (t : ℝ) (within : t ∈ Set.Ioc (p 0) (q 0)) : graphPoint chord t ∈ cell :=
      convex.segment_subset (T.inside 0) (T.inside (Fin.last n))
        (graphPoint_affine_mem_segment p_line.symm q_line.symm
          (Set.Icc_subset_uIcc (Set.Ioc_subset_Icc_self within)))
    have ribbon := graphRibbons_subset_convex convex mem_trace mem_chord
    have sep := K.abs_signed_defects_sub_winding_le compact convex slopes level trace chord
      continuous.measurable (by dsimp [chord]; fun_prop) u ribbon weight bounded sign on_link
    have sum_h := T.hingeSum_eq_transport continuous affine m b
    have tri := abs_radialSectionHeading_sub_hingeAngleChange_le lt p_line q_line
    change _ ≤ (solidAngleMeasure (gnomonicNormal '' cell)).toReal + |p 0 * q 1 - q 0 * p 1| / 2
    rw [← sum_h] at sep
    have total := (abs_sub _ _).trans (add_le_add sep tri)
    convert total using 2 <;> ring
  · have eq : p 0 = q 0 := le_antisymm pq (le_of_not_gt lt)
    have coord (i : Fin (n + 1)) : T.path.vertex i 0 = p 0 := by
      have hlo := ordered (Fin.zero_le i)
      have hhi := ordered (Fin.le_last i)
      change p 0 ≤ T.path.vertex i 0 at hlo
      change T.path.vertex i 0 ≤ q 0 at hhi
      exact le_antisymm (hhi.trans_eq eq.symm) hlo
    have vertex_eq (i : Fin n) : T.path.vertex i.succ = T.path.vertex i.castSucc := by
      apply sub_eq_zero.mp
      apply T.flat
      change T.path.vertex i.succ 0 - T.path.vertex i.castSucc 0 = 0
      rw [coord i.succ, coord i.castSucc, sub_self]
    have all (i : Fin (n + 1)) : T.path.vertex i = p := by
      refine Fin.induction rfl (fun i hi => (vertex_eq i).trans hi) i
    have same : q = p := all (Fin.last n)
    have turns : T.hingeSum = 0 := by
      unfold hingeSum
      apply Finset.sum_eq_zero
      intro i _
      rw [hingeAngleChange, coord i.succ, coord i.castSucc, sub_self]
    have empty : graphRibbon trace trace (p 0) (p 0) = ∅ := by
      simp [graphRibbon, Set.Ioc_self]
    have winding (z : ℝ × ℝ) : normalRibbonWinding trace trace (p 0) (p 0) z = 0 := by
      unfold normalRibbonWinding
      rw [sub_self]
    have bound := K.abs_signed_defects_sub_winding_le compact convex slopes level trace trace
      continuous.measurable continuous.measurable (a := p 0) (b := p 0)
      (by simp) (by rw [empty, Set.empty_union]; exact Set.empty_subset _)
      weight bounded sign on_link
    simp only [winding, integral_zero, sub_zero] at bound
    change |(∑ v, weight v * C.interiorAngularDefect Set.univ v) + T.hingeSum -
      (radialSectionHeading (q 0) (q 1) - radialSectionHeading (p 0) (p 1))| ≤ _
    rw [same, turns, add_zero, sub_self, sub_zero]
    exact bound.trans (le_add_of_nonneg_right (by positivity))

end SupportedNormalTrace
end Unfoldings.ConvexRoof
