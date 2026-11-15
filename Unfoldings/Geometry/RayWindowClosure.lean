module

public import Unfoldings.Geometry.RayWindowTrimming
public import Unfoldings.Geometry.RadialWedgeClosure
public import Unfoldings.Geometry.StrictRadialTrimming
public import Unfoldings.Geometry.LinearPathBounds
public import Unfoldings.Geometry.PolygonalClosureEquations

/-! Construct actual supported Jordan closing links from a short radial source-ray window. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane (n + 2)) (source : Plane)

/-- A short actual window supplies its trims, supporting line, outward corner and Jordan closure. -/
theorem exists_supported_ray_window_closure (strict : source ∈ P.strictRadialSources)
    (initial : 0 < dist source (P.vertex 0))
    (last_nonzero : P.edge (Fin.last (n + 1)) ≠ 0)
    (genuine : ∀ i, P.internalSourceRay source i ≠ 0)
    (small : (∑ k : Fin n, InnerProductGeometry.angle
      (P.internalSourceRay source k.castSucc) (P.internalSourceRay source k.succ)) < Real.pi / 4) :
    ∃ a b : unitInterval, (0 < a.val ∧ a.val < 1) ∧ (0 < b.val ∧ b.val < 1) ∧
      ∃ (c : Plane) (height : Plane →ₗ[ℝ] ℝ),
        0 < dist source ((P.trimEnds a b).vertex 0) ∧
        dist source ((P.trimEnds a b).vertex 0) <
          dist source ((P.trimEnds a b).vertex (Fin.last (n + 2))) ∧
        (P.trimEnds a b).RadialFrom source 0 ∧
        (∀ z ∈ Set.range (P.trimEnds a b).path, 0 ≤ height (z - source)) ∧
        height (c - source) < 0 ∧
        0 < inner ℝ ((P.trimEnds a b).vertex (Fin.last (n + 2)) - source)
          (c - (P.trimEnds a b).vertex (Fin.last (n + 2))) ∧
        Schoenflies.IsJordanCurve ((P.trimEnds a b).threeSegmentClosure source c) := by
  obtain ⟨frame, a, b, first, last, quadrant⟩ :=
    P.exists_trimEnds_quadrant_of_internal_angle_sum source genuine small
  let Q := P.trimEnds a b
  have radial := P.radialFrom_of_strictRadialSource strict
  have Q_radial := P.trimEnds_radialFrom a b radial
  have Q_initial : 0 < dist source (Q.vertex 0) := by
    apply initial.trans_le
    exact (P.path_radius_bounds source radial
      (P.trimEnds_path_subset a b (Q.vertex_mem_path_range 0))).1
  have Q_progress := P.trimEnds_radius_progress a b radial last_nonzero last.1
  let left : Plane →ₗ[ℝ] ℝ := (LinearMap.fst ℝ ℝ ℝ).comp frame.symm.toLinearMap
  let right : Plane →ₗ[ℝ] ℝ := (LinearMap.snd ℝ ℝ ℝ).comp frame.symm.toLinearMap
  have supported_left (z : Plane) (member : z ∈ Set.range Q.path) : 0 ≤ left (z - source) :=
    Q.height_nonneg_on_path source left (fun j => (quadrant j).1.le) member
  have supported_right (z : Plane) (member : z ∈ Set.range Q.path) : 0 ≤ right (z - source) :=
    Q.height_nonneg_on_path source right (fun j => (quadrant j).2.le) member
  obtain ⟨c, excluded, outward, jordan⟩ := Q.exists_radial_wedge_closure source Q_radial Q_initial
    Q_progress frame (fun z member => ⟨supported_left z member, supported_right z member⟩)
  rcases excluded with negative | negative
  · exact ⟨a, b, first, last, c, left, Q_initial, Q_progress, Q_radial, supported_left,
      negative, outward, jordan⟩
  · exact ⟨a, b, first, last, c, right, Q_initial, Q_progress, Q_radial, supported_right,
      negative, outward, jordan⟩

end Unfoldings.PolygonalChain
