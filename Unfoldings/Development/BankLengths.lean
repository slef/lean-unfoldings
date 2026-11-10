module

public import Unfoldings.Development.SpatialLengths
public import Unfoldings.Development.BoundaryRays
public import Unfoldings.Complex.RelativeCutGraph

/-! Matched original-seam banks have equal actual developed lengths, in either direction. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

theorem germDirection_endpoint_reverse (edge : EdgeRef Face) (b : Bool) :
    F.germDirection (C.germOfEndpoint edge (!b)) =
      -F.germDirection (C.germOfEndpoint edge b) := by
  unfold germDirection
  rw [F.germFarPoint_germOfEndpoint, F.germFarPoint_germOfEndpoint]
  cases b <;> exact (neg_sub _ _).symm

theorem germDirection_endpoint_norm (edge : EdgeRef Face) (b : Bool) :
    ‖F.germDirection (C.germOfEndpoint edge b)‖ =
      ‖F.germDirection (C.germOfEndpoint edge false)‖ := by
  cases b
  · rfl
  · rw [show (true : Bool) = !false from rfl, F.germDirection_endpoint_reverse, norm_neg]

theorem germDirection_seam_norm (s : C.Seam) (side b : Bool) :
    ‖F.germDirection (C.germOfEndpoint (C.seamSide s side) b)‖ =
      ‖F.germDirection (C.germOfEndpoint (C.left s) false)‖ := by
  cases side
  · exact F.germDirection_endpoint_norm (C.left s) b
  · have crossing : C.GermCrosses Set.univ (C.germOfEndpoint (C.right s) b)
        (C.germOfEndpoint (C.left s) (C.acrossEndpoint s true b)) :=
      ⟨s, Set.mem_univ _, true, b, rfl, rfl⟩
    have same := F.germDirection_mate Set.univ (C.germOfEndpoint (C.right s) b)
    rw [C.mateGerm_of_crossing crossing] at same
    change ‖F.germDirection (C.germOfEndpoint (C.right s) b)‖ = _
    rw [← same]
    exact F.germDirection_endpoint_norm (C.left s) _

end Unfoldings.SpatialFolding

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (F : SpatialFolding C)

/-- The bank label alone determines its genuine edge length, independent of the endpoint choice. -/
theorem boundaryRay_norm_seam (p : C.BoundaryEnd retain) (s : C.Seam) (side : Bool)
    (edge : C.germEdge p.val = C.seamSide s side) :
    ‖D.boundaryRay p‖ = ‖F.germDirection (C.germOfEndpoint (C.left s) false)‖ := by
  have raw : p.val = C.germOfEndpoint (C.seamSide s side) p.val.2 := by
    rw [← edge]
    exact (C.germOfEndpoint_germEdge p.val).symm
  have length := D.germRay_norm_eq_spatial F
    (⟨p.val, rfl⟩ : C.LinkGerm retain (C.boundaryEndVertex retain p))
  change ‖D.boundaryRay p‖ = ‖F.germDirection p.val‖ at length
  rw [length, raw]
  exact F.germDirection_seam_norm s side p.val.2

include F in
/-- Two banks of the same original seam have exactly equal developed lengths. -/
theorem boundaryRay_norm_eq_of_seam (p q : C.BoundaryEnd retain) (s : C.Seam)
    (a b : Bool) (first : C.germEdge p.val = C.seamSide s a)
    (last : C.germEdge q.val = C.seamSide s b) :
    ‖D.boundaryRay p‖ = ‖D.boundaryRay q‖ :=
  (D.boundaryRay_norm_seam F p s a first).trans (D.boundaryRay_norm_seam F q s b last).symm

end Unfoldings.FacewiseDevelopment
