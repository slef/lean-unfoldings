module

public import Unfoldings.Cone.Charts
public import Unfoldings.Cone.TangentShortcut
public import Unfoldings.Path.LocalShortcut

/-!
# Geodesics avoid positive-curvature interior vertices

The constructed whole-ball tangent chart transfers the strict apex shortcut
to the original intrinsic metric. Continuity and geodesic injectivity then
exclude a visit at every interior parameter of a nonconstant shortest path.
Convexity is not assumed: the hypothesis is the actual strict total-angle
bound, to be derived separately from embedded convex geometry.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.TriangleComplex.TangentChart

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} {v : C.Vertex retain} (N : C.TangentChart retain v)

theorem chart_origin
    (h : C.tangentOrigin retain v ∈
      Metric.eball (C.tangentOrigin retain v) (ENNReal.ofReal N.radius)) :
    (N.chart ⟨C.tangentOrigin retain v, h⟩).val = C.vertexPoint retain v := by
  obtain ⟨p⟩ := C.nonempty_linkGerm retain v
  let c : C.CornerAt retain v := ⟨p.val.1, p.property⟩
  let a : C.TangentTotal retain v := ⟨c, C.tangentApex retain v c⟩
  have apex : C.tangentPoint retain v a = C.tangentOrigin retain v :=
    (C.tangentOrigin_eq retain v c).symm
  have near : edist (C.tangentPoint retain v a) (C.tangentOrigin retain v) <
      ENNReal.ofReal N.radius := by rw [apex]; exact h
  have same : (⟨C.tangentPoint retain v a, near⟩ :
      Metric.eball (C.tangentOrigin retain v) (ENNReal.ofReal N.radius)) =
        ⟨C.tangentOrigin retain v, h⟩ := Subtype.ext apex
  calc
    (N.chart ⟨C.tangentOrigin retain v, h⟩).val = C.tangentSurfaceTag retain v a :=
      (congrArg (fun z => (N.chart z).val) same).symm.trans (N.agrees a near)
    _ = C.faceMap retain c.val.1
        ⟨(C.triangle c.val.1).vertex c.val.2, (C.triangle c.val.1).vertex_mem c.val.2⟩ :=
      C.tangentSurfaceTag_of_mem retain v a ((C.triangle c.val.1).vertex_mem c.val.2)
    _ = C.vertexPoint retain v := (C.vertexPoint_eq_cornerAt retain v c).symm

theorem edist_lt_via_vertex (interior : ¬ C.IsBoundaryVertex retain v)
    (positive_curvature : C.totalAngle retain v < 2 * Real.pi)
    (x : C.Realization retain)
    (hx : x ∈ Metric.eball (C.vertexPoint retain v) (ENNReal.ofReal N.radius))
    (y : C.Realization retain)
    (hy : y ∈ Metric.eball (C.vertexPoint retain v) (ENNReal.ofReal N.radius))
    (left_nonzero : x ≠ C.vertexPoint retain v) (right_nonzero : y ≠ C.vertexPoint retain v) :
    edist x y < edist x (C.vertexPoint retain v) + edist (C.vertexPoint retain v) y := by
  have radius : 0 < ENNReal.ofReal N.radius := ENNReal.ofReal_pos.mpr N.positive
  let ox : Metric.eball (C.tangentOrigin retain v) (ENNReal.ofReal N.radius) :=
    ⟨C.tangentOrigin retain v, Metric.mem_eball_self radius⟩
  let os : Metric.eball (C.vertexPoint retain v) (ENNReal.ofReal N.radius) :=
    ⟨C.vertexPoint retain v, Metric.mem_eball_self radius⟩
  have center : N.chart ox = os := Subtype.ext (N.chart_origin ox.property)
  let z := N.chart.symm ⟨x, hx⟩
  let w := N.chart.symm ⟨y, hy⟩
  have left_image : N.chart z = ⟨x, hx⟩ := N.chart.apply_symm_apply _
  have right_image : N.chart w = ⟨y, hy⟩ := N.chart.apply_symm_apply _
  have z_nonzero : z.val ≠ C.tangentOrigin retain v := by
    intro zero
    have equal : z = ox := Subtype.ext zero
    have images := congrArg (fun q => (N.chart q).val) equal
    rw [left_image, center] at images
    exact left_nonzero images
  have w_nonzero : w.val ≠ C.tangentOrigin retain v := by
    intro zero
    have equal : w = ox := Subtype.ext zero
    have images := congrArg (fun q => (N.chart q).val) equal
    rw [right_image, center] at images
    exact right_nonzero images
  have strict := C.tangent_edist_lt_via_origin retain v interior positive_curvature
    z.val w.val z_nonzero w_nonzero
  change edist z w < edist z ox + edist ox w at strict
  rw [← N.chart.isometry.edist_eq z w, ← N.chart.isometry.edist_eq z ox,
    ← N.chart.isometry.edist_eq ox w, left_image, right_image, center] at strict
  exact strict

end Unfoldings.TriangleComplex.TangentChart

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (retain : Set C.Seam) (v : C.Vertex retain)

include F

/-- Every nonconstant geodesic avoids a positive-curvature interior vertex
at all interior parameter times. The local metric chart is constructed. -/
theorem geodesic_ne_positive_vertex (interior : ¬ C.IsBoundaryVertex retain v)
    (positive_curvature : C.totalAngle retain v < 2 * Real.pi)
    {a b : C.Realization retain} {p : Path a b} (geodesic : p.IsGeodesic)
    (distinct : a ≠ b) (t : unitInterval) (time : t ∈ Set.Ioo (0 : unitInterval) 1) :
    p t ≠ C.vertexPoint retain v := by
  let N := F.tangentChart retain v
  exact geodesic.ne_of_local_shortcuts distinct (C.vertexPoint retain v)
    (ENNReal.ofReal N.radius) (ENNReal.ofReal_pos.mpr N.positive)
    (N.edist_lt_via_vertex interior positive_curvature) t time

end Unfoldings.SpatialFolding
