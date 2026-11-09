module

public import Unfoldings.Source.PieceFormula
public import Unfoldings.Complex.FaceRouteEnd
public import Unfoldings.Complex.InteriorTags

/-!
# Finite actual terminal-face formulas, including tied endpoints

Every shortest path has a final positive-length face interval. Its constructed
motion belongs to the finite candidate family and gives its whole terminal
radial formula, including the endpoint. At a face-interior endpoint the final
face is necessarily that original face, by exact seam identifications.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem exists_source_terminal_piece :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (base : C.PointFiber Set.univ source) (p : SourcePath source),
      ∃ f : Face, ∃ y : C.Cell f, C.faceMap Set.univ f y = p.target ∧
        ∃ A ∈ P.sourceMotionCandidates R base,
          ∃ a : unitInterval, a < 1 ∧ ∀ t : unitInterval, a ≤ t →
            F.toSpace Set.univ (p.path t) =
              F.place f (A.symm ((t : ℝ) • R.coordinate p.path p.geodesic)) := by
  let := P.metricSpace
  intro source R base p
  obtain ⟨route, _bound⟩ := F.exists_geodesic_faceRoute P.embedded p.geodesic
  let i := route.lastIndex
  obtain ⟨A, member, formula⟩ := P.exists_source_piece_formula R base p route i
  have target : C.faceMap Set.univ (route.face i) (route.exit i) = p.target := by
    rw [route.exit_image, route.last_end_time, Path.target]
  refine ⟨route.face i, route.exit i, target, A, member,
    route.time i.castSucc, route.last_entry_lt_one, ?_⟩
  intro t after
  let h := Path.intervalFraction (route.time i.castSucc) 1 t route.last_entry_lt_one
    ⟨after, t.property.2⟩
  have time : Path.intervalParam (route.time i.castSucc) (route.time i.succ) h = t := by
    rw [route.last_end_time]
    exact Path.intervalParam_fraction _ _ _ _ _
  have image : C.faceMap Set.univ (route.face i) (F.faceRoutePiecePath route i h) = p.path t :=
    (F.faceRoutePiecePath_image route i h).trans (congrArg p.path time)
  have coordinate := formula h
  rw [time] at coordinate
  have inverse : (F.faceRoutePiecePath route i h).val =
      A.symm ((t : ℝ) • R.coordinate p.path p.geodesic) := by
    rw [← coordinate, A.symm_apply_apply]
  calc
    F.toSpace Set.univ (p.path t) =
        F.toSpace Set.univ (C.faceMap Set.univ (route.face i) (F.faceRoutePiecePath route i h)) :=
      congrArg (F.toSpace Set.univ) image.symm
    _ = F.place (route.face i) (F.faceRoutePiecePath route i h).val := F.toSpace_faceMap _ _ _
    _ = _ := congrArg (F.place (route.face i)) inverse

theorem exists_source_terminal_formula_in_face :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (base : C.PointFiber Set.univ source) (f : Face) (x : C.Cell f),
      x.val ∈ interior (C.triangle f).carrier → ∀ p : SourcePath source,
        p.target = C.faceMap Set.univ f x →
          ∃ A ∈ P.sourceMotionCandidates R base,
            ∃ a : unitInterval, a < 1 ∧ ∀ t : unitInterval, a ≤ t →
              F.toSpace Set.univ (p.path t) =
                F.place f (A.symm ((t : ℝ) • R.coordinate p.path p.geodesic)) := by
  let := P.metricSpace
  intro source R base f x inside p target
  obtain ⟨g, y, image, A, member, a, before, formula⟩ := P.exists_source_terminal_piece R base p
  have tags : (⟨f, x⟩ : C.Total) = ⟨g, y⟩ :=
    C.faceInterior_tag_eq Set.univ f x inside ⟨g, y⟩ (target.symm.trans image.symm)
  have faces := congrArg Sigma.fst tags
  change f = g at faces
  subst g
  exact ⟨A, member, a, before, formula⟩

end Unfoldings.SpatialFolding.ConvexBoundary
