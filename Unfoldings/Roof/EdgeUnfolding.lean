module

public import Unfoldings.Roof.UniformOriginalNonoverlap
public import Unfoldings.Roof.SectorForestExistence
public import Unfoldings.Roof.Tilt

/-! Every sufficiently shallow acute convex roof has a nonoverlapping original-edge cut disk. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

/-- The threshold depends only on the acute margin. Boundary heights and the presence of
interior mesh vertices are unrestricted. Closed-boundary injectivity is a further conclusion. -/
theorem exists_uniform_nonoverlapping_edge_unfolding {α : ℝ} (positive : 0 < α) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C),
        AcuteMargin (C := C) α → K.TiltBound φ →
          ∃ retain : Set C.Seam,
            (C.relativeCutGraph retain Set.univ).IsRootedForest (C.relativeCutRoots Set.univ) ∧
            ∃ disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1,
              ∃ D : FacewiseDevelopment C retain, D.Nonoverlapping ∧
                ∀ x, ‖(disk x).val‖ < 1 → ∃ r > 0,
                  Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => D.toPlane y.val) := by
  obtain ⟨φforest, forest_bounds, t, t_bounds, forest⟩ :=
    exists_uniform_tilt_sectorForest.{u, v} positive
  obtain ⟨φgeometry, geometry_bounds, nonoverlap⟩ :=
    exists_uniform_original_sector_nonoverlap.{u, v} t t_bounds.1 (by linarith [t_bounds.2])
  let φ := min φforest φgeometry
  have φpositive : 0 < φ := lt_min forest_bounds.1 geometry_bounds.1
  have φsmall : φ < Real.pi / 2 := (min_le_left _ _).trans_lt forest_bounds.2
  refine ⟨φ, ⟨φpositive, φsmall⟩, ?_⟩
  intro Face _ C K acute tilt
  have tilt_forest : K.TiltBound φforest :=
    TiltBound.of_le K tilt φpositive.le (by linarith [forest_bounds.2, Real.pi_pos])
      (min_le_left _ _)
  have tilt_geometry : K.TiltBound φgeometry :=
    TiltBound.of_le K tilt φpositive.le (by linarith [geometry_bounds.2, Real.pi_pos])
      (min_le_right _ _)
  obtain ⟨origin, ⟨M⟩⟩ := forest K acute tilt_forest
  obtain ⟨D, local_isometry⟩ := M.exists_locally_isometric_development
  exact ⟨M.retain, M.rootedForest, M.cutDisk, D,
    nonoverlap K tilt_geometry M D, local_isometry⟩

end Unfoldings.ConvexRoof
