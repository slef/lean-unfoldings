module

public import Unfoldings.Cap.UniformOriginalNonoverlap
public import Unfoldings.Cap.SectorForestExistence
public import Unfoldings.Cap.RoofInteriorHeight
public import Unfoldings.Cap.NoInterior
public import Unfoldings.Cap.FlatMetric
public import Unfoldings.Cap.Tilt

/-!
# Original-edge nonoverlap for nearly flat convex caps

A positive acute margin determines a positive tilt threshold before the mesh.
Only original input seams are cut. The cuts form a boundary-rooted forest,
the intrinsic cut surface is a closed disk, and an actual facewise development
is locally isometric throughout the open disk and has disjoint face interiors.
Boundary injectivity and the paper's running-time bound are separate assertions.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

theorem exists_edge_unfolding_of_flat {Face : Type u} [Fintype Face]
    {C : TriangleComplex.{u, v} Face} (K : ConvexCap C) (flat : K.TiltBound 0) :
    ∃ retain : Set C.Seam,
      (C.relativeCutGraph retain Set.univ).IsRootedForest (C.relativeCutRoots Set.univ) ∧
      ∃ disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1,
        ∃ E : FacewiseDevelopment C retain, E.Nonoverlapping ∧
          ∀ x, ‖(disk x).val‖ < 1 → ∃ r > 0,
            Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => E.toPlane y.val) := by
  refine ⟨Set.univ, K.folding.rootedForest_no_new_cuts Set.univ K.diskHomeomorph,
    K.diskHomeomorph, K.flatDevelopment flat, K.flatDevelopment_nonoverlapping flat, ?_⟩
  intro x _inside
  exact ⟨1, zero_lt_one, (K.flatDevelopment_isometry flat).comp isometry_subtype_coe⟩

/-- A mesh-independent positive threshold for the original-edge nonoverlap conclusion. -/
theorem exists_uniform_nonoverlapping_edge_unfolding {α : ℝ} (positive : 0 < α) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        AcuteMargin (C := C) α → K.TiltBound φ →
          ∃ retain : Set C.Seam,
            (C.relativeCutGraph retain Set.univ).IsRootedForest (C.relativeCutRoots Set.univ) ∧
            ∃ disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1,
              ∃ E : FacewiseDevelopment C retain, E.Nonoverlapping ∧
                ∀ x, ‖(disk x).val‖ < 1 → ∃ r > 0,
                  Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => E.toPlane y.val) := by
  classical
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
  by_cases internal : ∃ v : C.Vertex Set.univ, ¬ C.IsBoundaryVertex Set.univ v
  · obtain ⟨origin, origin_internal, ⟨M⟩⟩ := forest K acute tilt_forest internal
    rcases K.flat_or_positive_interior_roof with flat | positive_height
    · exact K.exists_edge_unfolding_of_flat flat
    · obtain ⟨E, local_isometry⟩ := M.exists_locally_isometric_development
      refine ⟨M.retain, M.rootedForest, M.cutDisk, E, ?_, local_isometry⟩
      exact nonoverlap K tilt_geometry M origin_internal
        (positive_height _ ((K.projectedVertex_mem_interior_iff origin).mpr origin_internal)) E
  · apply K.exists_edge_unfolding_of_flat
    apply K.flat_of_no_interior
    intro v
    exact Classical.not_not.mp (fun nonboundary => internal ⟨v, nonboundary⟩)

end Unfoldings.ConvexCap
