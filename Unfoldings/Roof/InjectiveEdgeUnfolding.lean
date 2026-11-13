module

public import Unfoldings.Roof.EdgeUnfolding
public import Unfoldings.Roof.OriginalSectorFrames
public import Unfoldings.Roof.UniformOriginalAllRadiusContact
public import Unfoldings.Roof.PrunedAllVertexContact
public import Unfoldings.Roof.PrunedDevelopmentLocalIsometry
public import Unfoldings.Roof.UniformCurvature

/-!
Uniformly shallow acute arbitrary-rim roofs admit globally injective original-edge unfoldings.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

/-- Prune precisely the flat descendant cuts. The resulting actual intrinsic closed disk
has an injective development, while every remaining cut is an original input seam. -/
theorem exists_uniform_injective_edge_unfolding {α : ℝ} (positive : 0 < α) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C),
        AcuteMargin (C := C) α → K.TiltBound φ →
          ∃ retain : Set C.Seam,
            (C.relativeCutGraph retain Set.univ).IsRootedForest (C.relativeCutRoots Set.univ) ∧
            ∃ disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1,
              ∃ D : FacewiseDevelopment C retain, D.Nonoverlapping ∧
                (∀ x, ‖(disk x).val‖ < 1 → ∃ r > 0,
                  Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => D.toPlane y.val)) ∧
                Function.Injective D.toPlane := by
  obtain ⟨φforest, forest_bounds, t, t_bounds, forest⟩ :=
    exists_uniform_tilt_sectorForest.{u, v} positive
  have tsmall : t < 1 := by linarith [t_bounds.2]
  obtain ⟨φnonoverlap, nonoverlap_bounds, nonoverlap⟩ :=
    exists_uniform_original_sector_nonoverlap.{u, v} t t_bounds.1 tsmall
  obtain ⟨φcontact, contact_bounds, contacts⟩ :=
    exists_uniform_original_sector_all_radius_contact.{u, v} t t_bounds.1 tsmall
  obtain ⟨φframe, frame_bounds, frames⟩ :=
    exists_uniform_original_sectorFrameData.{u, v} t t_bounds.1 tsmall
  obtain ⟨φcurvature, curvature_bounds, curvature⟩ :=
    exists_uniform_tilt_totalCurvature_lt.{u, v} Real.pi_pos
  let φ := min φforest (min φnonoverlap (min φcontact (min φframe φcurvature)))
  have φpositive : 0 < φ := lt_min forest_bounds.1
    (lt_min nonoverlap_bounds.1 (lt_min contact_bounds.1
      (lt_min frame_bounds.1 curvature_bounds.1)))
  have φsmall : φ < Real.pi / 2 := (min_le_left _ _).trans_lt forest_bounds.2
  refine ⟨φ, ⟨φpositive, φsmall⟩, ?_⟩
  intro Face _ C K acute tilt
  have widen {θ : ℝ} (small : θ < Real.pi / 2) (ordered : φ ≤ θ) : K.TiltBound θ :=
    TiltBound.of_le K tilt φpositive.le (by linarith [Real.pi_pos]) ordered
  have tilt_forest := widen forest_bounds.2 (min_le_left _ _)
  have tilt_nonoverlap := widen nonoverlap_bounds.2
    ((min_le_right _ _).trans (min_le_left _ _))
  have tilt_contact := widen contact_bounds.2
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have tilt_frame := widen frame_bounds.2
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have tilt_curvature := widen curvature_bounds.2
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨origin, ⟨M⟩⟩ := forest K acute tilt_forest
  obtain ⟨D, _local_isometry⟩ := M.exists_locally_isometric_development
  have separated := nonoverlap K tilt_nonoverlap M D
  have physical := contacts K tilt_contact M D
  obtain ⟨B⟩ := frames K tilt_frame M D
  have budget := curvature K tilt_curvature
  exact ⟨M.curvedRetain, M.curved_rootedForest, M.curvedCutDisk,
    M.curvedDevelopment D separated, separated, M.curvedDevelopment_local_isometry D separated,
    B.curvedDevelopment_injective separated budget physical⟩

end Unfoldings.ConvexRoof
