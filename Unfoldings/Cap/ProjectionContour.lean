module

public import Unfoldings.Cap.ProjectionFrame
public import Unfoldings.Cap.SubtreeAngles
public import Unfoldings.Development.BoundaryFrame

/-!
# Actual boundary contours oriented by the original cap projection

The cycle's first outgoing corner is chosen positive in projection. The
previously checked whole-subtree bank rotations then use a common complex frame
whose orientation agrees with the actual projection on every developed face.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Signed corner area in the actual horizontal projection, starting along the raw germ. -/
def projectedGermOrientation (p : C.Germ) : ℝ :=
  orient (K.projectFace p.1.1 ((C.triangle p.1.1).vertex p.1.2))
    (K.projectFace p.1.1 ((C.triangle p.1.1).vertex (C.germFarCorner p).2))
    (K.projectFace p.1.1 ((C.triangle p.1.1).vertex (C.germFarCorner (C.turnGerm p)).2))

theorem projectedGermOrientation_ne_zero (p : C.Germ) : K.projectedGermOrientation p ≠ 0 := by
  obtain ⟨⟨f, i⟩, side⟩ := p
  cases side
  · exact (K.projectedTriangle f).orient_edge_ne_zero i
  · have reverse : K.projectedGermOrientation ((f, i), true) =
        -K.projectedGermOrientation ((f, i), false) := by
      simp only [projectedGermOrientation, TriangleComplex.germFarCorner,
        TriangleComplex.turnGerm, Bool.not_true, Bool.not_false]
      unfold orient
      ring
    rw [reverse]
    exact neg_ne_zero.mpr ((K.projectedTriangle f).orient_edge_ne_zero i)

theorem projectedGermOrientation_bank_end (edge : EdgeRef Face) (b : Bool) :
    K.projectedGermOrientation (C.germOfEndpoint edge (!b)) =
      -K.projectedGermOrientation (C.germOfEndpoint edge b) := by
  obtain ⟨f, i⟩ := edge
  cases b <;> fin_cases i <;>
    simp [projectedGermOrientation, TriangleComplex.germOfEndpoint,
      TriangleComplex.germFarCorner, TriangleComplex.turnGerm, Triangle.next, orient] <;> ring

theorem projectedGermOrientation_boundaryTurn {retain : Set C.Seam}
    (p : C.BoundaryEnd retain) :
    K.projectedGermOrientation (C.boundaryTurn retain p).val =
      -K.projectedGermOrientation p.val := by
  obtain ⟨⟨bank, b⟩, rfl⟩ := (C.boundaryEndEquiv retain).symm.surjective p
  simp only [TriangleComplex.boundaryTurn, Equiv.apply_symm_apply]
  exact K.projectedGermOrientation_bank_end bank.val b

/-- The actual bank cycle can be oriented positively without assuming any planar nonoverlap. -/
theorem exists_projection_positive_contour (retain : Set C.Seam)
    (connected : (C.boundaryGraph retain).adjacencyGraph.Connected) :
    ∃ contour : C.BoundaryContour retain,
      0 < K.projectedGermOrientation contour.cycle.first.val := by
  obtain ⟨n, c, closes, covers⟩ := C.exists_boundaryCycle_cover_of_connected retain connected
  have exists_start : ∃ p : C.BoundaryEnd retain, 0 < K.projectedGermOrientation p.val := by
    by_cases positive : 0 < K.projectedGermOrientation c.first.val
    · exact ⟨c.first, positive⟩
    · refine ⟨C.boundaryTurn retain c.first, ?_⟩
      rw [K.projectedGermOrientation_boundaryTurn]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt positive)
        (K.projectedGermOrientation_ne_zero c.first.val))
  obtain ⟨p, positive⟩ := exists_start
  obtain ⟨m, cycle, starts, closed⟩ := C.exists_boundaryCycle retain p
  exact ⟨⟨m, cycle, closed,
    C.boundaryCycle_covers_of_connected retain cycle closed connected⟩, starts.symm ▸ positive⟩

namespace SectorForest

variable {K} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- The actual cut disk is dually connected, independently of its possibly overlapping image. -/
theorem duallyConnected : C.DuallyConnected M.retain := by
  let : ConnectedSpace (Metric.closedBall (0 : Plane) 1) :=
    isConnected_iff_connectedSpace.mp
      ((convex_closedBall (0 : Plane) 1).isConnected ⟨0, Metric.mem_closedBall_self zero_le_one⟩)
  let : ConnectedSpace (C.Realization M.retain) :=
    M.cutDisk.symm.surjective.connectedSpace M.cutDisk.symm.continuous
  exact C.duallyConnected_of_preconnected M.retain

/-- A covering boundary contour chosen using the actual horizontal projection. -/
def projectionContour : C.BoundaryContour M.retain :=
  Classical.choose (K.exists_projection_positive_contour M.retain
    (K.folding.boundaryGraph_connected_of_disk M.retain M.cutDisk))

theorem projectionContour_positive :
    0 < K.projectedGermOrientation M.projectionContour.cycle.first.val :=
  Classical.choose_spec (K.exists_projection_positive_contour M.retain
    (K.folding.boundaryGraph_connected_of_disk M.retain M.cutDisk))

end SectorForest
end Unfoldings.ConvexCap

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

theorem germOrientation_eq_projected (p : C.Germ) :
    D.germOrientation p = orientationScale (D.projectedPlacement K p.1.1).toAffineMap *
      K.projectedGermOrientation p :=
  D.projectedPlacement_orient K p.1.1 _ _ _

/-- Positive projected orientation selects exactly the global projection-preserving frame. -/
theorem boundaryCycleFrame_eq_projectionFrame {n : ℕ}
    (cycle : (C.boundarySystem retain).Chain n)
    (positive : 0 < K.projectedGermOrientation cycle.first.val) :
    D.boundaryCycleFrame cycle =
      (D.projectionFrame K cycle.first.val.1.1).trans Complex.orthonormalBasisOneI.repr.symm := by
  have sign : (0 < D.germOrientation cycle.first.val) ↔
      0 < orientationScale (D.projectedPlacement K cycle.first.val.1.1).toAffineMap := by
    rw [D.germOrientation_eq_projected K]
    exact mul_pos_iff_of_pos_right positive
  unfold boundaryCycleFrame projectionFrame
  by_cases first : 0 < D.germOrientation cycle.first.val
  · rw [ite_eq_left first, ite_eq_left (sign.mp first)]
    rfl
  · rw [ite_eq_right first, ite_eq_right (fun h => first (sign.mpr h))]

end Unfoldings.FacewiseDevelopment
