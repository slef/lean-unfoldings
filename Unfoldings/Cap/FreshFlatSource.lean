module

public import Unfoldings.Cap.FreshSourceStar
public import Unfoldings.Complex.Curvature
public import Unfoldings.Cone.IntervalBankClosure

/-! Zero-curvature fresh sources are completed by closing the two actual full-turn banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (frontier : P.ParentFrontier) (vertex : C.Vertex Set.univ) (fresh : vertex ∉ frontier.processed)

include K roots fresh in
/-- An actual zero-curvature fresh-source star needs no inserted positive sector. Closing
only its two original equal-radius banks produces the exact plane metric, preserving all
original angular corner placements. -/
theorem exists_fresh_flat_source_closed_plane
    (flat : C.interiorAngularDefect Set.univ vertex = 0) :
    let retain := C.processedParentRetain S (frontier.process vertex)
    ∃ w : C.Vertex retain, C.vertexForgetCuts (Set.subset_univ retain) w = vertex ∧
    C.totalAngle retain w = 2 * Real.pi ∧
    ∃ n, ∃ c : (C.linkSystem retain w).Chain n,
    ∃ covers : ∀ p, c.Visited p,
    ∃ start : C.linkMate retain w c.first = c.first,
    ∃ finish : C.linkMate retain w (C.linkTurn retain w c.last) = C.linkTurn retain w c.last,
    ∃ F : C.ClosedIntervalTangentFan retain w c covers start finish ≃ᵢ ℂ,
      ∀ x : (C.linkAngularFan retain w c).Surface,
        F (C.closeIntervalTangentFan retain w c covers start finish
          (C.angularToTangent retain w c x)) = (C.linkAngularFan retain w c).develop x := by
  classical
  dsimp only
  let retain := C.processedParentRetain S (frontier.process vertex)
  obtain ⟨w, boundary, original, full_angle, _unique⟩ :=
    K.exists_fresh_source_cut_star S roots frontier vertex fresh
  obtain ⟨n, c, start, finish, covers⟩ := C.exists_interval_link retain w boundary
  have nonroot : vertex ∉ P.roots := fun root => fresh (frontier.roots root)
  have internal : ¬ C.IsBoundaryVertex Set.univ vertex := by
    simpa only [roots, TriangleComplex.relativeCutRoots, Set.mem_ofPred_eq] using nonroot
  have curvature : C.interiorAngularDefect Set.univ vertex =
      2 * Real.pi - C.totalAngle Set.univ vertex := by
    simp only [TriangleComplex.interiorAngularDefect, ite_eq_right internal]
  have full : C.totalAngle retain w = 2 * Real.pi := by
    rw [curvature] at flat
    rw [full_angle]
    linarith
  exact ⟨w, original, full, n, c, covers, start, finish,
    C.intervalBankClosurePlaneIsometryEquiv retain w c covers start finish full,
    C.intervalBankClosurePlane_angularToTangent retain w c covers start finish full⟩

end Unfoldings.ConvexCap
