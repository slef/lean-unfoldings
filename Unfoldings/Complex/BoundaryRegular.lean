module

public import Unfoldings.Complex.BoundaryQuotient
public import Unfoldings.Complex.Regular
public import Unfoldings.Geometry.TriangleBoundary

/-!
# Nonvertex points away from the cut banks are regular

A representative is either in a face interior or on a retained edge. A spatial
folding guarantees the two incident faces of a retained seam are distinct.
Thus every nonvertex point off the actual bank boundary has a Euclidean metric
ball chart, for any retained seam set and without convexity assumptions.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

include F in
theorem isRegularPoint_of_not_bankBoundary_of_not_vertex (retain : Set C.Seam)
    (x : C.Realization retain) (outside : x ∉ C.bankBoundary retain)
    (nonvertex : x ∉ Set.range (C.vertexPoint retain)) : C.IsRegularPoint retain x := by
  have hinge (s : C.Seam) (kept : s ∈ retain)
      (q : (C.triangle (C.left s).face).Edge (C.left s).edge)
      (point : MetricGluing.point C.Cell (C.glue retain) (C.edgePoint (C.left s) q) = x) :
      C.IsRegularPoint retain x := by
    have regular : ¬ (C.triangle (C.left s).face).IsVertex q := by
      intro vertex
      apply nonvertex
      rw [← point]
      exact (C.mem_range_vertexPoint_iff retain _).mpr vertex
    rw [← point]
    exact C.isRegularPoint_hinge retain s kept (F.incident_faces_ne s) q regular
  obtain ⟨⟨f, p⟩, image⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) x
  by_cases inside : p.val ∈ interior (C.triangle f).carrier
  · rw [← image]
    exact C.isRegularPoint_face retain f p inside
  obtain ⟨e, on_edge⟩ := (C.triangle f).exists_edge_of_not_mem_interior p inside
  have attached : ∃ s ∈ retain, C.Incident s ⟨f, e⟩ := by
    by_contra boundary
    let bank : C.BoundaryBank retain := ⟨⟨f, e⟩, boundary⟩
    apply outside
    rw [← image]
    exact C.bankMap_mem_bankBoundary retain bank ⟨p.val, on_edge⟩
  obtain ⟨s, kept, side | side⟩ := attached
  · have face : f = (C.left s).face := congrArg EdgeRef.face side
    have edge : e = (C.left s).edge := congrArg EdgeRef.edge side
    subst f
    subst e
    exact hinge s kept ⟨p.val, on_edge⟩ image
  · have face : f = (C.right s).face := congrArg EdgeRef.face side
    have edge : e = (C.right s).edge := congrArg EdgeRef.edge side
    subst f
    subst e
    let right : (C.triangle (C.right s).face).Edge (C.right s).edge := ⟨p.val, on_edge⟩
    have equal := C.seam_identified retain s kept ((C.identify s).symm right)
    rw [(C.identify s).apply_symm_apply] at equal
    exact hinge s kept ((C.identify s).symm right) (equal.trans image)

end Unfoldings.SpatialFolding
