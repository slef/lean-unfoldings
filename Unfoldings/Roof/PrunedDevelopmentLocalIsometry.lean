module

public import Unfoldings.Roof.CurvaturePrunedDevelopment

/-! The actual development obtained by restoring flat cuts is locally isometric on the open disk. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)

open Classical in
theorem curvedDevelopment_local_isometry (D : FacewiseDevelopment C M.retain)
    (nonoverlap : D.Nonoverlapping) :
    ∀ x, ‖(M.curvedCutDisk x).val‖ < 1 → ∃ r > 0,
      Isometry (fun y : Metric.eball x (ENNReal.ofReal r) =>
        (M.curvedDevelopment D nonoverlap).toPlane y.val) := by
  obtain ⟨E, _nonoverlap, local_isometry⟩ :=
    M.exists_curved_nonoverlapping_local_development D nonoverlap
  let : PreconnectedSpace (Metric.closedBall (0 : Plane) 1) :=
    Subtype.preconnectedSpace (convex_closedBall (0 : Plane) 1).isPreconnected
  let : PreconnectedSpace (C.Realization M.curvedRetain) :=
    M.curvedCutDisk.symm.surjective.denseRange.preconnectedSpace M.curvedCutDisk.symm.continuous
  obtain ⟨root⟩ := K.nonempty_face
  let motion := (E.place root).symm.trans ((M.curvedDevelopment D nonoverlap).place root)
  have same : E.postcompose motion = M.curvedDevelopment D nonoverlap :=
    (E.normalize root ((M.curvedDevelopment D nonoverlap).place root)).eq_of_root
      (M.curvedDevelopment D nonoverlap) (C.duallyConnected_of_preconnected M.curvedRetain)
      root (E.normalize_root root _)
  intro x inside
  obtain ⟨r, positive, isometric⟩ := local_isometry x inside
  have transported := E.isometry_postcompose motion isometric
  rw [same] at transported
  exact ⟨r, positive, transported⟩

end Unfoldings.ConvexRoof.SectorForest
