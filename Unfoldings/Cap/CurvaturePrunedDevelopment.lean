module

public import Unfoldings.Cap.CurvaturePrunedForest
public import Unfoldings.Cap.CurvatureCutDevelopment
public import Unfoldings.Development.NonoverlapNormalization

/-! Pruning flat subtrees preserves necessary curvature cuts and interior local isometry. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

open Classical in
theorem curved_cut_curvature (v : C.Vertex Set.univ)
    (positive : 0 < C.interiorAngularDefect Set.univ v) :
    ∃ s b, s ∉ M.curvedRetain ∧ v = C.seamVertex s b := by
  have nonroot : v ∉ M.parents.roots := by
    intro root
    have boundary := (Set.ext_iff.mp M.roots_eq v).mp root
    change C.IsBoundaryVertex Set.univ v at boundary
    have zero : C.interiorAngularDefect Set.univ v = 0 := by
      simp only [TriangleComplex.interiorAngularDefect, ite_eq_left boundary]
    exact (ne_of_gt positive) zero
  have bound : C.interiorAngularDefect Set.univ v ≤ M.subtreeCurvature v :=
    Finset.single_le_sum (fun w _ => K.interiorCurvature_nonneg w)
      ((M.parents.mem_descendants v v).mpr (M.parents.ancestor_refl v))
  have curved : 0 < M.subtreeCurvature v := positive.trans_le bound
  let e : {w : C.Vertex Set.univ // w ∉ M.curvedParents.roots} :=
    ⟨v, fun root => root.elim nonroot (ne_of_gt curved)⟩
  have cut : M.curvedSelection.edge e ∉ M.curvedRetain := fun kept => kept ⟨e, rfl⟩
  rcases M.curvedSelection.link e with first | last
  · exact ⟨M.curvedSelection.edge e, false, cut, first.1⟩
  · exact ⟨M.curvedSelection.edge e, true, cut, last.1⟩

open Classical in
theorem exists_curved_nonoverlapping_local_development (D : FacewiseDevelopment C M.retain)
    (nonoverlap : D.Nonoverlapping) :
    ∃ E : FacewiseDevelopment C M.curvedRetain, E.Nonoverlapping ∧
      ∀ x, ‖(M.curvedCutDisk x).val‖ < 1 → ∃ r > 0,
        Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => E.toPlane y.val) := by
  obtain ⟨E, local_isometry⟩ := K.exists_development_of_curvature_cut_disk M.curvedRetain
    M.curvedCutDisk M.curved_cut_curvature
  let : PreconnectedSpace (Metric.closedBall (0 : Plane) 1) :=
    Subtype.preconnectedSpace (convex_closedBall (0 : Plane) 1).isPreconnected
  let : PreconnectedSpace (C.Realization M.curvedRetain) :=
    M.curvedCutDisk.symm.surjective.denseRange.preconnectedSpace M.curvedCutDisk.symm.continuous
  obtain ⟨root⟩ := K.nonempty_face
  have transfer := E.nonoverlapping_iff_of_duallyConnected (M.curvedDevelopment D nonoverlap)
    (C.duallyConnected_of_preconnected M.curvedRetain) root
  exact ⟨E, transfer.mpr (M.curvedDevelopment_nonoverlapping D nonoverlap), local_isometry⟩

end Unfoldings.ConvexCap.SectorForest
