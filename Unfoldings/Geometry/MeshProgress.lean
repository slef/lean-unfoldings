module

public import Unfoldings.Geometry.AcuteProgress
public import Mathlib.Order.Filter.Finite

/-!
# An outgoing input edge in a planar acute mesh

A finite closed triangle cover and actual corner incidence suffice. Near the
center only incident triangles occur. A point just ahead in the quadrant lies
in one of those triangles; its acute corner supplies an original incident edge.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

open Filter Topology

/-- In a finite closed cover, a sufficiently near piece also contains the center. -/
theorem eventually_piece_contains_center {X I : Type*} [TopologicalSpace X] [Finite I]
    (pieces : I → Set X) (closed : ∀ i, IsClosed (pieces i)) (center : X) :
    ∀ᶠ p in 𝓝 center, ∀ i, p ∈ pieces i → center ∈ pieces i := by
  classical
  apply Filter.eventually_all.mpr
  intro i
  by_cases present : center ∈ pieces i
  · exact Filter.Eventually.of_forall (fun _ _ => present)
  · filter_upwards [(closed i).isOpen_compl.mem_nhds present] with p outside inside
    exact (outside inside).elim

/-- Every neighborhood contains a positive point of any prescribed ray. -/
theorem exists_positive_ray_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (center direction : E) (s : Set E) (near : s ∈ 𝓝 center) :
    ∃ t : ℝ, 0 < t ∧ center + t • direction ∈ s := by
  have continuous : Continuous (fun t : ℝ => center + t • direction) := by fun_prop
  have tends : Tendsto (fun t : ℝ => center + t • direction) (𝓝 0) (𝓝 center) := by
    simpa only [zero_smul, add_zero] using continuous.continuousAt.tendsto (x := 0)
  obtain ⟨δ, positive, bound⟩ := Metric.eventually_nhds_iff.mp (tends.eventually near)
  refine ⟨δ / 2, half_pos positive, bound ?_⟩
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos positive)] using
    (show δ / 2 < δ by linarith)

/-- A genuine triangle edge enters the strict quadrant at every interior mesh vertex. -/
theorem exists_mesh_quadrant_edge {Face : Type*} [Finite Face] (triangle : Face → Triangle)
    (region : Set Plane) (cover : region ⊆ ⋃ f, (triangle f).carrier) (center : Plane)
    (inside : center ∈ interior region)
    (corner : ∀ f, center ∈ (triangle f).carrier → ∃ i, (triangle f).vertex i = center)
    (acute : ∀ f i, (triangle f).cornerAngle i < Real.pi / 2) :
    ∃ f i, (triangle f).vertex i = center ∧
      (StrictQuadrant ((triangle f).vertex (Triangle.next i) - center) ∨
        StrictQuadrant ((triangle f).vertex (Triangle.next (Triangle.next i)) - center)) := by
  have star := eventually_piece_contains_center (fun f => (triangle f).carrier)
    (fun f => (triangle f).compact_carrier.isClosed) center
  have near : {p | p ∈ region ∧ ∀ f, p ∈ (triangle f).carrier →
      center ∈ (triangle f).carrier} ∈ 𝓝 center := by
    filter_upwards [star, isOpen_interior.mem_nhds inside] with p hp interior
    exact ⟨interior_subset interior, hp⟩
  let direction : Plane := WithLp.toLp 2 ![1, 1]
  obtain ⟨t, positive, present, star⟩ := exists_positive_ray_mem center direction _ near
  obtain ⟨f, face⟩ := Set.mem_iUnion.mp (cover present)
  obtain ⟨i, vertex⟩ := corner f (star f face)
  refine ⟨f, i, vertex, ?_⟩
  have ahead : StrictQuadrant ((center + t • direction) - (triangle f).vertex i) := by
    rw [vertex, add_sub_cancel_left]
    simpa only [StrictQuadrant, direction, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_toLp,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_one] using
      And.intro positive positive
  simpa only [vertex] using (triangle f).exists_incident_quadrant_edge i (acute f i)
    (center + t • direction) face ahead

end Unfoldings
