module

public import Unfoldings.Source.FiniteMotions
public import Unfoldings.Source.FacePathMotion
public import Unfoldings.Path.SubpathBounds

/-!
# Exact finite rigid formulas along every actual shortest-path face piece

All proper prefixes avoid the cut locus. The actual motion stays fixed
along the retained portion of a face piece. Continuity extends its radial
formula through the terminal endpoint, even when that endpoint is cut or
singular. Its rigid motion belongs to the already constructed finite family.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem exists_source_piece_formula :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (base : C.PointFiber Set.univ source) (p : SourcePath source)
      (route : C.FaceRoute p.path) (i : Fin route.steps),
      ∃ A ∈ P.sourceMotionCandidates R base, ∀ t : unitInterval,
        A (F.faceRoutePiecePath route i t).val =
          (Path.intervalParam (route.time i.castSucc) (route.time i.succ) t : ℝ) •
            R.coordinate p.path p.geodesic := by
  let := P.metricSpace
  intro source R base p route i
  let Q := F.faceRoutePiecePath route i
  let time := Path.intervalParam (route.time i.castSucc) (route.time i.succ)
  have ordered : route.time i.castSucc < route.time i.succ := route.increasing Fin.castSucc_lt_succ
  have before_time (t : unitInterval) (before : t < 1) : time t < 1 :=
    (Path.intervalParam_lt_right ordered before).trans_le (route.time i.succ).property.2
  have off (t : unitInterval) (before : t < 1) :
      C.faceMap Set.univ (route.face i) (Q t) ∉ sourceCutLocus source := by
    rw [F.faceRoutePiecePath_image]
    exact P.sourcePath_proper_prefix_not_cutLocus R p (time t) (before_time t before)
  let x : P.sourceFaceRegion source (route.face i) := ⟨Q 0, off 0 zero_lt_one⟩
  let A := P.sourceFaceMotion R (route.face i) x
  have member : A ∈ P.sourceMotionCandidates R base :=
    P.sourceTaggedMotion_mem_candidates R base ⟨route.face i, Q 0⟩ (off 0 zero_lt_one)
  have proper (t : unitInterval) (before : t < 1) :
      A (Q t).val = (time t : ℝ) • R.coordinate p.path p.geodesic := by
    have inside (u : unitInterval) :
        C.faceMap Set.univ (route.face i) (Q.subpath 0 t u) ∉ sourceCutLocus source := by
      exact off (Path.intervalParam 0 t u)
        ((Path.intervalParam_mem_Icc t.property.1 u).2.trans_lt before)
    have same_motion := P.sourceFaceMotion_eq_along_path R (route.face i) (Q.subpath 0 t)
      inside (off 0 zero_lt_one) (off t before)
    have outside_prefix : (p.initial (time t)).target ∉ sourceCutLocus source :=
      P.sourcePath_proper_prefix_not_cutLocus R p (time t) (before_time t before)
    have point : (⟨C.faceMap Set.univ (route.face i) (Q t), off t before⟩ :
        ↥((sourceCutLocus source)ᶜ)) = ⟨(p.initial (time t)).target, outside_prefix⟩ :=
      Subtype.ext (F.faceRoutePiecePath_image route i t)
    have coordinate : P.sourceFaceCoordinates R (route.face i) ⟨Q t, off t before⟩ =
        (time t : ℝ) • R.coordinate p.path p.geodesic := by
      change R.coordinatesOffCutLocus (P.sourcePath_target_surjective source)
        ⟨C.faceMap Set.univ (route.face i) (Q t), off t before⟩ = _
      rw [point]
      exact (R.coordinate_of_sourcePath_off_cut (P.sourcePath_target_surjective source)
        (p.initial (time t)) outside_prefix).trans (R.coordinate_initial p (time t))
    rw [P.sourceFaceCoordinates_eq_motion R (route.face i), ← same_motion] at coordinate
    exact coordinate
  have closed : IsClosed {t : unitInterval |
      A (Q t).val = (time t : ℝ) • R.coordinate p.path p.geodesic} :=
    isClosed_eq ((A.continuous.comp continuous_subtype_val).comp Q.continuous)
      ((continuous_subtype_val.comp (Path.continuous_intervalParam _ _)).smul continuous_const)
  refine ⟨A, member, ?_⟩
  intro t
  exact closure_minimal proper closed (Path.dense_proper_unitInterval_times t)

end Unfoldings.SpatialFolding.ConvexBoundary
