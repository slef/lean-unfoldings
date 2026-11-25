module

public import Unfoldings.Roof.GraphRegionFans
public import Unfoldings.Roof.RestrictedBoundaryCover
public import Unfoldings.Geometry.MarkedPointConstraints
public import Unfoldings.Geometry.AffineSupportBoundary
public import Mathlib.Order.Interval.Set.Infinite

/-! Each actual interior graph contact has one selected original boundary fan. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

open Filter Topology

/-- The boundary of a local upper graph region is its graph. -/
theorem mem_frontier_of_local_epigraph {f : ℝ → ℝ} (hf : Continuous f) {S : Set Plane}
    {p : Plane} (on_graph : p 1 = f (p 0))
    (near : ∀ᶠ z in 𝓝 p, z ∈ S ↔ f (z 0) ≤ z 1) :
    p ∈ frontier S := by
  refine ⟨subset_closure (near.self_of_nhds.mpr on_graph.ge), ?_⟩
  intro inside
  obtain ⟨ε, positive, agrees⟩ := Metric.eventually_nhds_iff_ball.mp near
  let h := graphShear f hf
  let U := h '' (interior S ∩ Metric.ball p ε)
  have open_U : IsOpen U := h.isOpenMap _ (isOpen_interior.inter Metric.isOpen_ball)
  have point_U : h p ∈ U := ⟨p, ⟨inside, Metric.mem_ball_self positive⟩, rfl⟩
  let T := {z : Plane | 0 ≤ z 1}
  have included : U ⊆ T := by
    rintro z ⟨q, ⟨q_in, close⟩, rfl⟩
    exact (graphShear_mem_halfPlane_iff f hf q).mpr ((agrees q close).mp (interior_subset q_in))
  let O : Plane := 0
  have no_interior : h p ∉ interior T := by
    apply not_mem_interior_of_affine_lower_bound (pointCoordinateEquation O 1)
      (pointCoordinateEquation_ne_zero O 1)
    · intro z hz
      have nonneg : 0 ≤ z 1 := hz
      simpa only [pointCoordinateEquation_apply, O, PiLp.zero_apply, sub_zero] using nonneg
    · change (p 1 - f (p 0)) - 0 = 0
      rw [on_graph, sub_self, sub_zero]
  exact no_interior (open_U.subset_interior_iff.mpr included point_U)

end Unfoldings.PlanarTopology

namespace Unfoldings.ConvexRoof

open Filter Topology PlanarTopology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
  (sample : Face → Plane) (sample_in : ∀ i, sample i ∈ interior (K.projectedTriangle i).carrier)
  (endpoints : ∀ i z, z ∈ interior (K.projectedTriangle i).carrier → z 0 ≠ a ∧ z 0 ≠ b)
  (aligned : ∀ i, Disjoint (interior (K.projectedTriangle i).carrier) (graphPoint f '' Set.Icc a b))

local notation "Above" => facesAboveGraph sample f a b

include hf sample_in endpoints aligned

/-- Every interior graph point lies on the geometric boundary of the upper face region. -/
theorem mem_frontier_facesAboveGraph {p : Plane} (inside : p ∈ interior K.footprint)
    (window : p 0 ∈ Set.Ioo a b) (on_graph : p 1 = f (p 0)) :
    p ∈ frontier (K.restrictedCarrier Above) :=
  mem_frontier_of_local_epigraph hf on_graph
    (K.eventually_restrictedCarrier_aboveGraph hf sample sample_in endpoints aligned inside window)

/-- Within the open horizontal window in the roof, no other boundary is introduced. -/
theorem eq_graph_of_mem_frontier_facesAboveGraph {p : Plane}
    (inside : p ∈ interior K.footprint) (window : p 0 ∈ Set.Ioo a b)
    (member : p ∈ frontier (K.restrictedCarrier Above)) : p 1 = f (p 0) := by
  let x := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0
  let y := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1
  have in_carrier := (K.compact_restrictedCarrier Above).isClosed.frontier_subset member
  refine le_antisymm ?_
    ((K.mem_restrictedCarrier_aboveGraph_iff hf sample sample_in endpoints aligned inside window).mp in_carrier)
  by_contra! strict
  apply member.2
  apply mem_interior_iff_mem_nhds.mpr
  have above : ∀ᶠ q in 𝓝 p, f (q 0) < q 1 :=
    (isOpen_lt (hf.comp x.continuous) y.continuous).mem_nhds strict
  filter_upwards [above, K.eventually_restrictedCarrier_aboveGraph hf sample sample_in
    endpoints aligned inside window] with q q_above q_region
  exact q_region.mpr q_above.le

set_option maxHeartbeats 1100000 in
open Classical in
/-- The actual upper fan exists at each aligned interior graph vertex and has
exactly its selected regional angles, including at transverse crossings. -/
theorem exists_boundaryEnd_facesAboveGraph (v : C.Vertex Set.univ)
    (inside : K.projectedVertex v ∈ interior K.footprint)
    (window : K.projectedVertex v 0 ∈ Set.Ioo a b)
    (on_graph : K.projectedVertex v 1 = f (K.projectedVertex v 0)) :
    ∃ p : (C.restrictFaces Above).BoundaryEnd Set.univ,
      C.includeRestrictedVertexUniv Above ((C.restrictFaces Above).boundaryEndVertex Set.univ p) = v ∧
      Cap.horizontal ((K.folding.restrictFaces Above).boundaryPosition p) = K.projectedVertex v ∧
      K.restrictedBoundaryTurnError Above p = -K.regionalAngleExcess Above v := by
  let p := K.projectedVertex v
  let prohibited := Set.range (fun k : Face × Fin 3 => (K.projectedTriangle k.1).vertex k.2 0)
  have finite : prohibited.Finite := Set.finite_range _
  have point : graphPoint f (p 0) = p := by
    ext j
    fin_cases j
    · rfl
    · exact on_graph.symm
  have limit : p ∈ closure (frontier (K.restrictedCarrier Above) \
      Set.range (fun i : Face × Fin 3 => (K.projectedTriangle i.1).vertex i.2)) := by
    apply Metric.mem_closure_iff.mpr
    intro ε ε_pos
    let V := (graphPoint f) ⁻¹' (Metric.ball p ε ∩ interior K.footprint) ∩ Set.Ioo a b
    have V_open : IsOpen V := ((Metric.isOpen_ball.inter isOpen_interior).preimage
      (continuous_graphPoint hf)).inter isOpen_Ioo
    have origin : p 0 ∈ V := by
      refine ⟨?_, window⟩
      change graphPoint f (p 0) ∈ Metric.ball p ε ∩ interior K.footprint
      rw [point]
      exact ⟨Metric.mem_ball_self ε_pos, inside⟩
    obtain ⟨ε', ε'_pos, included⟩ := Metric.isOpen_iff.mp V_open _ origin
    have ordered : p 0 - ε' < p 0 + ε' := by linarith only [ε'_pos]
    obtain ⟨t, t_in, safe⟩ := (Set.Ioo_infinite ordered).exists_notMem_finite finite
    have near : t ∈ Metric.ball (p 0) ε' := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith only [t_in.1, t_in.2]
    have ht := included near
    have z_in : graphPoint f t ∈ Metric.ball p ε ∩ interior K.footprint := ht.1
    refine ⟨graphPoint f t, ⟨K.mem_frontier_facesAboveGraph hf sample sample_in endpoints
      aligned z_in.2 ht.2 rfl, ?_⟩, ?_⟩
    · rintro ⟨i, equal⟩
      exact safe ⟨i, congrArg (fun x : Plane => x 0) equal⟩
    · rw [dist_comm]
      exact z_in.1
  obtain ⟨endPoint, original⟩ := K.exists_restricted_boundaryEnd_of_frontier_limit Above v limit
  have position : Cap.horizontal ((K.folding.restrictFaces Above).boundaryPosition endPoint) =
      K.projectedVertex v := by
    rw [(K.folding.restrictFaces Above).boundaryPosition_raw, ← original]
    exact (K.projectedVertex_ofCorner _ _).symm
  have unique (w : (C.restrictFaces Above).Vertex Set.univ)
      (equal : C.includeRestrictedVertexUniv Above w =
        C.includeRestrictedVertexUniv Above ((C.restrictFaces Above).boundaryEndVertex Set.univ endPoint)) :
      w = (C.restrictFaces Above).boundaryEndVertex Set.univ endPoint :=
    K.restricted_vertex_eq_of_punctured_neighborhood Above
      (fun _ r_pos => exists_punctured_epigraph_neighborhood hf on_graph
        (K.eventually_restrictedCarrier_aboveGraph hf sample sample_in endpoints aligned inside window) r_pos)
      _ _ (congrArg K.projectedVertex (equal.trans original)) (congrArg K.projectedVertex original)
  exact ⟨endPoint, original, position,
    (K.restrictedBoundaryTurnError_eq_neg_regional_of_unique Above endPoint unique).trans
      (congrArg (fun v => -K.regionalAngleExcess Above v) original)⟩

end Unfoldings.ConvexRoof
