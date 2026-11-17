module

public import Unfoldings.Geometry.RayWindowClosure
public import Unfoldings.Geometry.SupportedVertexAvoidingClosure

/-! Short source-ray windows give supported closures with original incidences controlled. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane (n + 2)) (source : Plane)

/-- The actual short-window geometry constructs both trims, an arbitrarily close regular
source and a supported Jordan closure, avoiding every prescribed original vertex and line. -/
theorem exists_supported_vertex_avoiding_ray_window_closure
    {ι κ : Type*} [Finite ι] [Finite κ]
    (strict : source ∈ P.strictRadialSources)
    (initial : 0 < dist source (P.vertex 0))
    (last_nonzero : P.edge (Fin.last (n + 1)) ≠ 0)
    (genuine : ∀ i, P.internalSourceRay source i ≠ 0)
    (small : (∑ k : Fin n, InnerProductGeometry.angle
      (P.internalSourceRay source k.castSucc) (P.internalSourceRay source k.succ)) < Real.pi / 4)
    (point : ι → Plane) (equation : κ → Plane →ᵃ[ℝ] ℝ) (proper : ∀ i, equation i ≠ 0)
    {δ : ℝ} (positive : 0 < δ) :
    ∃ a b : unitInterval, (0 < a.val ∧ a.val < 1) ∧ (0 < b.val ∧ b.val < 1) ∧
      ∃ (q c : Plane) (height : Plane →ₗ[ℝ] ℝ),
        let Q := P.trimEnds a b
        dist q source < δ ∧ Q.RadialFrom q 0 ∧
        0 < dist q (Q.vertex 0) ∧ dist q (Q.vertex 0) < dist q (Q.vertex (Fin.last (n + 2))) ∧
        (∀ z ∈ Set.range Q.path, 0 ≤ height (z - q)) ∧ height (c - q) < 0 ∧
        0 < inner ℝ (Q.vertex (Fin.last (n + 2)) - q) (c - Q.vertex (Fin.last (n + 2))) ∧
        (∀ i, equation i q ≠ 0 ∧ equation i c ≠ 0) ∧
        (∀ i, q ≠ point i ∧ c ≠ point i) ∧
        (∀ i, point i ∈ segment ℝ (Q.vertex 0) q → point i = Q.vertex 0) ∧
        (∀ i, point i ∉ segment ℝ q c) ∧
        (∀ i, point i ∈ segment ℝ (Q.vertex (Fin.last (n + 2))) c →
          point i = Q.vertex (Fin.last (n + 2))) ∧
        Schoenflies.IsJordanCurve (Q.threeSegmentClosure q c) := by
  obtain ⟨frame, a, b, first, last, quadrant⟩ :=
    P.exists_trimEnds_quadrant_of_internal_angle_sum source genuine small
  let Q := P.trimEnds a b
  have radial := P.radialFrom_of_strictRadialSource strict
  have trimmed_strict := P.strictRadialSource_trimEnds strict a b first.2 last.1
  have trimmed_initial : 0 < dist source (Q.vertex 0) := initial.trans_le
    (P.path_radius_bounds source radial (P.trimEnds_path_subset a b (Q.vertex_mem_path_range 0))).1
  have progress := P.trimEnds_radius_progress a b radial last_nonzero last.1
  obtain ⟨q, c, height, properties⟩ := Q.exists_supported_vertex_avoiding_wedge_closure
    source trimmed_strict trimmed_initial progress frame (fun j =>
      ⟨(quadrant j).1.le, (quadrant j).2.le⟩) point equation proper positive
  exact ⟨a, b, first, last, q, c, height, properties⟩

end Unfoldings.PolygonalChain
