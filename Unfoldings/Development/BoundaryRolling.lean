module

public import Unfoldings.Complex.BoundaryRolling
public import Unfoldings.Development.BoundaryRotations
public import Unfoldings.Development.BoundaryDisplacements
public import Unfoldings.Geometry.PolygonalLength
public import Unfoldings.Geometry.ComplexHeadingTransport

/-! Any actual development realizes the canonical rolled bank headings in one common frame. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (Q : C.BoundaryContour retain)

/-- The bank length is intrinsic data of the original face, independent of its placement. -/
theorem boundaryRay_norm (p : C.BoundaryEnd retain) :
    ‖D.boundaryRay p‖ = C.boundaryBankLength p := by
  rw [D.boundaryRay_eq_raw]
  change ‖D.place p.val.1.1 ((C.triangle p.val.1.1).vertex (C.germFarCorner p.val).2) -
    D.place p.val.1.1 ((C.triangle p.val.1.1).vertex p.val.1.2)‖ = _
  rw [← dist_eq_norm, (D.place p.val.1.1).isometry.dist_eq]
  rfl

/-- Actual developed bank vectors realize the canonical real, unreduced fan headings. -/
theorem normalized_boundaryRoll_heading (i : Fin (Q.length + 1)) :
    NormedSpace.normalize (D.boundaryCycleFrame Q.cycle (D.boundaryRay (Q.cycle.point i))) =
      polarRay ((D.boundaryCycleFrame Q.cycle (D.boundaryRay Q.cycle.first)).arg +
        C.boundaryRollHeading Q i) := by
  refine Fin.induction ?_ (fun k previous => ?_) i
  · rw [C.boundaryRollHeading_zero, add_zero]
    rw [show Q.cycle.point 0 = Q.cycle.first from rfl]
    exact complex_normalize_eq_polar_arg (by
      simpa only [map_zero] using (D.boundaryCycleFrame Q.cycle).injective.ne
        (D.boundaryRay_ne_zero Q.cycle.first))
  · have step := D.normalized_boundary_step Q.cycle Q.closes k.castSucc
    rw [show finRotate (Q.length + 1) k.castSucc = k.succ from
      finRotate_of_lt k.isLt] at step
    rw [step, previous, ← polarRay_add, C.boundaryRollHeading_succ]
    congr 1
    ring

/-- Roll and actual developed contour have the same edge vectors up to one initial rotation. -/
theorem boundaryRoll_edge_in_frame (i : Fin (Q.length + 1)) :
    D.boundaryCycleFrame Q.cycle (D.boundaryRay (Q.cycle.point i)) =
      polarRay ((D.boundaryCycleFrame Q.cycle (D.boundaryRay Q.cycle.first)).arg) *
        (C.boundaryRoll Q).edge i := by
  let L := D.boundaryCycleFrame Q.cycle
  have magnitude : ‖L (D.boundaryRay (Q.cycle.point i))‖ =
      C.boundaryBankLength (Q.cycle.point i) := by
    rw [L.norm_map, D.boundaryRay_norm]
  calc
    _ = ‖L (D.boundaryRay (Q.cycle.point i))‖ •
        NormedSpace.normalize (L (D.boundaryRay (Q.cycle.point i))) :=
      (NormedSpace.norm_smul_normalize _).symm
    _ = _ := by
      rw [magnitude, D.normalized_boundaryRoll_heading, TriangleComplex.boundaryRoll,
        PolygonalChain.ofHeadings_edge, polarRay_add, Complex.real_smul]
      ring

include D in
/-- A genuine global development forces the canonically rolled contour to close. -/
theorem boundaryRoll_closed :
    (C.boundaryRoll Q).vertex (Fin.last (Q.length + 1)) = 0 := by
  have total := congrArg (D.boundaryCycleFrame Q.cycle)
    (D.sum_boundaryRays_eq_zero Q.cycle Q.closes)
  simp only [map_sum, map_zero, D.boundaryRoll_edge_in_frame Q, ← Finset.mul_sum] at total
  have edges : (∑ i, (C.boundaryRoll Q).edge i) = 0 :=
    (mul_eq_zero.mp total).resolve_left (polarRay_ne_zero _)
  rw [(C.boundaryRoll Q).sum_edge, C.boundaryRoll_start Q, sub_zero] at edges
  exact edges

/-- All rolled bank vertices have exactly the actual developed positions in one rigid frame. -/
theorem boundaryRoll_vertex_in_frame (i : Fin (Q.length + 1)) :
    polarRay ((D.boundaryCycleFrame Q.cycle (D.boundaryRay Q.cycle.first)).arg) *
      (C.boundaryRoll Q).vertex i.castSucc =
        D.boundaryCycleFrame Q.cycle
          (D.boundaryPosition (Q.cycle.point i) - D.boundaryPosition Q.cycle.first) := by
  let P := C.boundaryRoll Q
  let L := D.boundaryCycleFrame Q.cycle
  let rotation := polarRay ((L (D.boundaryRay Q.cycle.first)).arg)
  change rotation * P.vertex i.castSucc =
    L (D.boundaryPosition (Q.cycle.point i) - D.boundaryPosition Q.cycle.first)
  refine Fin.induction ?_ (fun k previous => ?_) i
  · simp only [Fin.castSucc_zero, P, C.boundaryRoll_start Q, mul_zero]
    rw [show Q.cycle.point 0 = Q.cycle.first from rfl, sub_self, map_zero]
  · have vector := D.boundaryRoll_edge_in_frame Q k.castSucc
    change L (D.boundaryRay (Q.cycle.point k.castSucc)) = rotation * P.edge k.castSucc at vector
    rw [D.boundaryRay_eq_cycle_displacement Q.cycle Q.closes,
      show finRotate (Q.length + 1) k.castSucc = k.succ from finRotate_of_lt k.isLt] at vector
    rw [PolygonalChain.edge, Fin.succ_castSucc] at vector
    rw [map_sub] at vector ⊢
    rw [map_sub] at previous
    rw [mul_sub] at vector
    linear_combination previous - vector

end Unfoldings.FacewiseDevelopment
