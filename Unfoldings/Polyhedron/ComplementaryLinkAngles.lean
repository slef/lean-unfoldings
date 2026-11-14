module

public import Unfoldings.Polyhedron.IntervalLink
public import Unfoldings.Topology.PairedInvolutionExtension
public import Unfoldings.Topology.FinitePrefixSum
public import Unfoldings.Geometry.ClosedRayChain

/-! Both actual sides of an original interior vertex link control its spatial endpoint angle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) {retain : Set C.Seam} {v : C.Vertex retain} {n : ℕ}
  (c : (C.linkSystem retain v).Chain n)

/-- The unvisited complementary original corners bound the same genuine spatial endpoint angle. -/
theorem link_endpoint_angle_le_complement (internal : ¬ C.IsBoundaryVertex retain v) :
    InnerProductGeometry.angle (F.germDirection c.first.val)
      (F.germDirection (C.linkTurn retain v c.last).val) ≤
      C.totalAngle retain v -
        ∑ i : Fin (n + 1), (C.triangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2 := by
  have free (p : C.LinkGerm retain v) : C.linkMate retain v p ≠ p := fun fixed =>
    internal ((C.isBoundaryVertex_iff_linkMate_fixed retain v).mpr ⟨p, fixed⟩)
  obtain ⟨m, d, longer, kept, closed, covers⟩ := (C.linkSystem retain v).exists_cycle_extension
    (C.linkSystem_connected retain v) free c
  let weight (p : C.LinkGerm retain v) := (C.triangle p.val.1.1).cornerAngle p.val.1.2
  let big (i : Fin (m + 1)) := weight (d.point i)
  let small (i : Fin (n + 1)) := weight (c.point i)
  let ray := F.intervalLinkRay d
  have origin : ray 0 = F.germDirection d.first.val := by
    change F.intervalLinkRay d (0 : Fin (m + 1)).castSucc = _
    rw [F.intervalLinkRay_castSucc]
    rfl
  have same_origin : ray 0 = F.germDirection c.first.val := by
    rw [origin]
    exact congrArg (fun p : C.LinkGerm retain v => F.germDirection p.val) (kept 0)
  have closes : ray (Fin.last (m + 1)) = ray 0 := by
    rw [show ray (Fin.last (m + 1)) =
      F.germDirection (C.linkTurn retain v d.last).val from F.intervalLinkRay_last d, origin]
    have equal := congrArg (fun p : C.LinkGerm retain v => F.germDirection p.val) closed
    change F.germDirection (C.mateGerm retain (C.linkTurn retain v d.last).val) = _ at equal
    simpa only [F.germDirection_mate] using equal
  have angles (i : Fin (m + 1)) :
      InnerProductGeometry.angle (ray i.castSucc) (ray i.succ) = big i := by
    calc
      _ = InnerProductGeometry.angle (F.germDirection (d.point i).val)
          (F.germDirection (C.linkTurn retain v (d.point i)).val) :=
        congrArg₂ InnerProductGeometry.angle (F.intervalLinkRay_castSucc d i)
          (F.intervalLinkRay_succ d i)
      _ = big i := F.germDirection_angle (d.point i).val
  have total : (∑ i, big i) = C.totalAngle retain v :=
    C.sum_linkCornerAngle retain v d covers
  have prefix_sum : Fin.partialSum big ⟨n + 1, by omega⟩ = ∑ i, small i := by
    apply fin_partialSum_prefix (by omega : n + 1 ≤ m + 1) big small
    intro i
    exact congrArg weight (kept i)
  let endpoint : Fin (m + 2) := ⟨n + 1, by omega⟩
  let last_corner : Fin (m + 1) := ⟨n, by omega⟩
  have terminal : ray endpoint = F.germDirection (C.linkTurn retain v c.last).val := by
    rw [show endpoint = last_corner.succ from Fin.ext rfl]
    exact (F.intervalLinkRay_succ d last_corner).trans
      (congrArg (fun p : C.LinkGerm retain v =>
        F.germDirection (C.linkTurn retain v p).val) (kept (Fin.last n)))
  have estimate := angle_le_remaining_closed_ray_sum ray
    (by rw [origin]; exact F.germDirection_ne_zero _) closes endpoint
  simp only [angles] at estimate
  rw [total, prefix_sum, terminal, same_origin, InnerProductGeometry.angle_comm] at estimate
  exact estimate

end Unfoldings.SpatialFolding
