module

public import Unfoldings.Source.TaggedMotion
public import Unfoldings.Complex.FaceRouteLift

/-! Actual source motions stay fixed along every retained face-contained route piece. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem sourcePath_avoids_cut_of_target_off_cut :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (_R : SourceFrame source) (p : SourcePath source),
      p.target ∉ sourceCutLocus source → ∀ t, p.path t ∉ sourceCutLocus source := by
  let := P.metricSpace
  intro source R p outside t
  by_cases full : t = 1
  · simpa only [full, Path.target] using outside
  · exact P.sourcePath_proper_prefix_not_cutLocus R p t (lt_of_le_of_ne t.property.2 full)

theorem sourceFaceRoute_piece_motion :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      {a b : C.Realization Set.univ} {p : Path a b} (route : C.FaceRoute p),
      (∀ t, p t ∉ sourceCutLocus source) → ∀ i : Fin route.steps,
        ∀ entry_outside : C.faceMap Set.univ (route.face i) (route.entry i) ∉ sourceCutLocus source,
          ∀ exit_outside : C.faceMap Set.univ (route.face i) (route.exit i) ∉ sourceCutLocus source,
            P.sourceTaggedMotion R ⟨route.face i, route.entry i⟩ entry_outside =
              P.sourceTaggedMotion R ⟨route.face i, route.exit i⟩ exit_outside := by
  let := P.metricSpace
  intro source R a b p route outside i entry_outside exit_outside
  let Q := F.faceRoutePiecePath route i
  have inside (t : unitInterval) : Q t ∈ P.sourceFaceRegion source (route.face i) := by
    change C.faceMap Set.univ (route.face i) (Q t) ∉ sourceCutLocus source
    rw [F.faceRoutePiecePath_image]
    exact outside _
  let path := Q.codRestrict (P.sourceFaceRegion source (route.face i))
    entry_outside exit_outside inside
  have locally_constant := (P.sourceFaceMotion_locallyConstant R (route.face i)).comp_continuous
    path.continuous
  have equal := locally_constant.apply_eq_of_isPreconnected isPreconnected_univ
    (Set.mem_univ (0 : unitInterval)) (Set.mem_univ (1 : unitInterval))
  change P.sourceFaceMotion R (route.face i) ⟨route.entry i, entry_outside⟩ =
    P.sourceFaceMotion R (route.face i) ⟨route.exit i, exit_outside⟩
  simpa only [Function.comp_apply, Path.source, Path.target] using equal

end Unfoldings.SpatialFolding.ConvexBoundary
