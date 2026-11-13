module

public import Unfoldings.Roof.Boundary
public import Unfoldings.Topology.ParentPaths

/-! Place an interior source to the right of every interior mesh vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- A source can lie in the roof interior strictly to the right of every interior mesh vertex.
It need not be a vertex, so this also covers roofs triangulated using boundary vertices alone. -/
theorem exists_interior_forest_source :
    ∃ q ∈ interior K.footprint, ∀ v : C.Vertex Set.univ,
      ¬ C.IsBoundaryVertex Set.univ v → K.projectedVertex v 0 < q 0 := by
  classical
  by_cases nonempty : ∃ v : C.Vertex Set.univ, ¬ C.IsBoundaryVertex Set.univ v
  · let vertices := Finset.univ.filter
      (fun v : C.Vertex Set.univ => ¬ C.IsBoundaryVertex Set.univ v)
    have present : vertices.Nonempty := by
      obtain ⟨v, hv⟩ := nonempty
      exact ⟨v, by simp only [vertices, Finset.mem_filter, Finset.mem_univ, true_and]; exact hv⟩
    obtain ⟨v, hv, maximal⟩ := vertices.exists_max_image (fun v => K.projectedVertex v 0) present
    have internal : ¬ C.IsBoundaryVertex Set.univ v := (Finset.mem_filter.mp hv).2
    have inside := (K.projectedVertex_mem_interior_iff v).mpr internal
    obtain ⟨r, positive, ball⟩ := Metric.isOpen_iff.mp isOpen_interior (K.projectedVertex v) inside
    let q := K.projectedVertex v + EuclideanSpace.single 0 (r / 2)
    have near : q ∈ Metric.ball (K.projectedVertex v) r := by
      rw [Metric.mem_ball, dist_eq_norm]
      change ‖K.projectedVertex v + EuclideanSpace.single 0 (r / 2) - K.projectedVertex v‖ < r
      rw [add_sub_cancel_left, PiLp.norm_single, Real.norm_eq_abs,
        abs_of_pos (half_pos positive)]
      linarith
    refine ⟨q, ball near, ?_⟩
    intro w internal_w
    have bound := maximal w (by
      simp only [vertices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact internal_w)
    have coordinate : q 0 = K.projectedVertex v 0 + r / 2 := by simp [q, EuclideanSpace.single]
    rw [coordinate]
    linarith
  · obtain ⟨q, inside⟩ := K.interior_projection
    exact ⟨q, inside, fun v internal => (nonempty ⟨v, internal⟩).elim⟩

end Unfoldings.ConvexRoof
