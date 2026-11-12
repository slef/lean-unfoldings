module

public import Unfoldings.Cap.EdgeUnfolding
public import Unfoldings.Cap.SectorQuadrants
public import Unfoldings.Cap.UniformOriginalAllRadiusContact
public import Unfoldings.Cap.PrunedVertexContactFibers
public import Unfoldings.Cap.PrunedDevelopmentLocalIsometry

/-! Nearly flat caps admit an original-edge unfolding injective away from intrinsic vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- A uniform original-edge unfolding whose only possible contacts are intrinsic
vertex copies over the same original physical vertex. -/
theorem exists_uniform_edge_unfolding_same_original_vertex_contacts {α : ℝ} (positive : 0 < α) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        AcuteMargin (C := C) α → K.TiltBound φ →
          ∃ retain : Set C.Seam,
            (C.relativeCutGraph retain Set.univ).IsRootedForest (C.relativeCutRoots Set.univ) ∧
            ∃ disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1,
              ∃ E : FacewiseDevelopment C retain, E.Nonoverlapping ∧
                (∀ x, ‖(disk x).val‖ < 1 → ∃ r > 0,
                  Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => E.toPlane y.val)) ∧
                ∀ x y, E.toPlane x = E.toPlane y →
                  x = y ∨ ∃ v w : C.Vertex retain,
                    C.vertexPoint retain v = x ∧ C.vertexPoint retain w = y ∧
                      C.vertexForgetCuts (Set.subset_univ _) v =
                        C.vertexForgetCuts (Set.subset_univ _) w := by
  classical
  obtain ⟨φforest, forest_bounds, t, t_bounds, forest⟩ :=
    exists_uniform_sectorForest_internal_sectorFrameData.{u, v} positive
  have tsmall : t < 1 := by linarith [t_bounds.2]
  obtain ⟨φnonoverlap, nonoverlap_bounds, nonoverlap⟩ :=
    exists_uniform_original_sector_nonoverlap.{u, v} t t_bounds.1 tsmall
  obtain ⟨φcontact, contact_bounds, contacts⟩ :=
    exists_uniform_original_sector_all_radius_contact.{u, v} t t_bounds.1 tsmall
  let φ := min φforest (min φnonoverlap φcontact)
  have φpositive : 0 < φ := lt_min forest_bounds.1
    (lt_min nonoverlap_bounds.1 contact_bounds.1)
  have φsmall : φ < Real.pi / 2 := (min_le_left _ _).trans_lt forest_bounds.2
  refine ⟨φ, ⟨φpositive, φsmall⟩, ?_⟩
  intro Face _ C K acute tilt
  have tilt_forest : K.TiltBound φforest :=
    TiltBound.of_le K tilt φpositive.le (by linarith [forest_bounds.2, Real.pi_pos])
      (min_le_left _ _)
  have tilt_nonoverlap : K.TiltBound φnonoverlap :=
    TiltBound.of_le K tilt φpositive.le (by linarith [nonoverlap_bounds.2, Real.pi_pos])
      ((min_le_right _ _).trans (min_le_left _ _))
  have tilt_contact : K.TiltBound φcontact :=
    TiltBound.of_le K tilt φpositive.le (by linarith [contact_bounds.2, Real.pi_pos])
      ((min_le_right _ _).trans (min_le_right _ _))
  have flat_case (flat : K.TiltBound 0) :
      ∃ retain : Set C.Seam,
        (C.relativeCutGraph retain Set.univ).IsRootedForest (C.relativeCutRoots Set.univ) ∧
        ∃ disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1,
          ∃ E : FacewiseDevelopment C retain, E.Nonoverlapping ∧
            (∀ x, ‖(disk x).val‖ < 1 → ∃ r > 0,
              Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => E.toPlane y.val)) ∧
            ∀ x y, E.toPlane x = E.toPlane y →
                  x = y ∨ ∃ v w : C.Vertex retain,
                    C.vertexPoint retain v = x ∧ C.vertexPoint retain w = y ∧
                      C.vertexForgetCuts (Set.subset_univ _) v =
                        C.vertexForgetCuts (Set.subset_univ _) w := by
    refine ⟨Set.univ, K.folding.rootedForest_no_new_cuts Set.univ K.diskHomeomorph,
      K.diskHomeomorph, K.flatDevelopment flat, K.flatDevelopment_nonoverlapping flat, ?_, ?_⟩
    · intro x _inside
      exact ⟨1, zero_lt_one, (K.flatDevelopment_isometry flat).comp isometry_subtype_coe⟩
    · intro x y same
      exact Or.inl ((K.flatDevelopment_isometry flat).injective same)
  by_cases internal : ∃ v : C.Vertex Set.univ, ¬ C.IsBoundaryVertex Set.univ v
  · obtain ⟨origin, M, origin_internal, budget, frames⟩ := forest K acute tilt_forest internal
    rcases K.flat_or_positive_interior_roof with flat | positive_height
    · exact flat_case flat
    · have source_height := positive_height _
        ((K.projectedVertex_mem_interior_iff origin).mpr origin_internal)
      obtain ⟨D, _local_isometry⟩ := M.exists_locally_isometric_development
      have separated := nonoverlap K tilt_nonoverlap M origin_internal source_height D
      obtain ⟨positive_t, small_t, ⟨B⟩⟩ := frames D
      have physical := contacts K tilt_contact M origin_internal source_height D
      refine ⟨M.curvedRetain, M.curved_rootedForest, M.curvedCutDisk,
        M.curvedDevelopment D separated, separated,
        M.curvedDevelopment_local_isometry D separated, ?_⟩
      exact SectorForest.curved_contact_eq_or_same_original_vertices B separated budget physical
  · exact flat_case (K.flat_of_no_interior fun v =>
      Classical.not_not.mp (fun nonboundary => internal ⟨v, nonboundary⟩))

end Unfoldings.ConvexCap
