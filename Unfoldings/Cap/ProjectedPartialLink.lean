module

public import Unfoldings.Cap.ProjectedInterval
public import Unfoldings.Topology.PairedInvolutionExtension
public import Unfoldings.Topology.FinitePrefixSum
public import Unfoldings.Geometry.ClosedRayChain

/-! Both sides of actual projected partial corner fans bound their endpoint angle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {v : C.Vertex Set.univ} {n : ℕ} (c : (C.linkSystem Set.univ v).Chain n)

/-- The selected and complementary projected angles bound the same actual endpoint angle. -/
theorem projected_partial_link_angle_bounds (internal : ¬ C.IsBoundaryVertex Set.univ v) :
    let angle := InnerProductGeometry.angle (K.projectedGermRay c.first)
      (K.projectedGermRay (C.linkTurn Set.univ v c.last))
    let selected := ∑ i : Fin (n + 1),
      (K.projectedTriangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2
    angle ≤ selected ∧ angle ≤ K.projectedTotalAngle Set.univ v - selected := by
  have partial_first : K.projectedIntervalRay c 0 = K.projectedGermRay c.first := by
    change K.projectedIntervalRay c (0 : Fin (n + 1)).castSucc = _
    rw [K.projectedIntervalRay_castSucc]
    rfl
  have direct := angle_endpoint_le_sum (K.projectedIntervalRay c)
    (K.projectedIntervalRay_ne_zero c 0)
  rw [partial_first, K.projectedIntervalRay_last] at direct
  simp only [K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ,
    K.projectedGermRay_angle] at direct
  refine ⟨direct, ?_⟩
  have free (p : C.LinkGerm Set.univ v) : C.linkMate Set.univ v p ≠ p := fun fixed =>
    internal ((C.isBoundaryVertex_iff_linkMate_fixed Set.univ v).mpr ⟨p, fixed⟩)
  obtain ⟨m, d, longer, kept, closed, covers⟩ := (C.linkSystem Set.univ v).exists_cycle_extension
    (C.linkSystem_connected Set.univ v) free c
  let weight (p : C.LinkGerm Set.univ v) := (K.projectedTriangle p.val.1.1).cornerAngle p.val.1.2
  let big (i : Fin (m + 1)) := weight (d.point i)
  let small (i : Fin (n + 1)) := weight (c.point i)
  let ray := K.projectedIntervalRay d
  have origin : ray 0 = K.projectedGermRay d.first := by
    change K.projectedIntervalRay d (0 : Fin (m + 1)).castSucc = _
    rw [K.projectedIntervalRay_castSucc]
    rfl
  have same_origin : ray 0 = K.projectedGermRay c.first := by
    rw [origin]
    exact congrArg K.projectedGermRay (kept 0)
  have closes : ray (Fin.last (m + 1)) = ray 0 := by
    rw [show ray (Fin.last (m + 1)) = K.projectedGermRay (C.linkTurn Set.univ v d.last) from
      K.projectedIntervalRay_last d, origin]
    have equal := congrArg K.projectedGermRay closed
    change K.projectedGermRay (C.linkMate Set.univ v (C.linkTurn Set.univ v d.last)) =
      K.projectedGermRay d.first at equal
    simpa only [K.projectedGermRay_mate] using equal
  have angles (i : Fin (m + 1)) :
      InnerProductGeometry.angle (ray i.castSucc) (ray i.succ) = big i := by
    calc
      _ = InnerProductGeometry.angle (K.projectedGermRay (d.point i))
          (K.projectedGermRay (C.linkTurn Set.univ v (d.point i))) :=
        congrArg₂ InnerProductGeometry.angle (K.projectedIntervalRay_castSucc d i)
          (K.projectedIntervalRay_succ d i)
      _ = big i := K.projectedGermRay_angle (d.point i)
  have total : (∑ i, big i) = K.projectedTotalAngle Set.univ v :=
    K.projectedLinkFan_totalAngle d covers
  have prefix_sum : Fin.partialSum big ⟨n + 1, by omega⟩ = ∑ i, small i := by
    apply fin_partialSum_prefix (by omega : n + 1 ≤ m + 1) big small
    intro i
    exact congrArg weight (kept i)
  let endpoint : Fin (m + 2) := ⟨n + 1, by omega⟩
  let last_corner : Fin (m + 1) := ⟨n, by omega⟩
  have terminal : ray endpoint = K.projectedGermRay (C.linkTurn Set.univ v c.last) := by
    rw [show endpoint = last_corner.succ from Fin.ext rfl]
    exact (K.projectedIntervalRay_succ d last_corner).trans
      (congrArg (fun p : C.LinkGerm Set.univ v => K.projectedGermRay (C.linkTurn Set.univ v p))
        (kept (Fin.last n)))
  have estimate := angle_le_remaining_closed_ray_sum ray
    (K.projectedIntervalRay_ne_zero d 0) closes endpoint
  simp only [angles] at estimate
  rw [total, prefix_sum, terminal, same_origin, InnerProductGeometry.angle_comm] at estimate
  exact estimate

end Unfoldings.ConvexCap
