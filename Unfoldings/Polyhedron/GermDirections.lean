module

public import Unfoldings.Polyhedron.GermSpatial
public import Unfoldings.Geometry.PlaneIntersection

/-!
# Actual radial directions and noncoplanar seam planes

The nonzero direction of a germ belongs to its rigid face plane and is
preserved by seam mates. If the two planes differ, their intersection is
exactly this direction line. Every direction shared by both planes is
therefore parallel to the actual seam ray.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

def germDirection (p : C.Germ) : Space :=
  F.germFarPoint p - F.place p.1.1 ((C.triangle p.1.1).vertex p.1.2)

theorem germDirection_ne_zero (p : C.Germ) : F.germDirection p ≠ 0 :=
  sub_ne_zero.mpr (F.germFarPoint_ne_apex p)

theorem germDirection_mem_range (p : C.Germ) :
    F.germDirection p ∈ LinearMap.range (F.place p.1.1).linear := by
  refine ⟨(C.triangle p.1.1).vertex (C.germFarCorner p).2 -
    (C.triangle p.1.1).vertex p.1.2, ?_⟩
  exact (F.place p.1.1).toAffineMap.linear_apply_vsub _ _

theorem germDirection_mate (retain : Set C.Seam) (p : C.Germ) :
    F.germDirection (C.mateGerm retain p) = F.germDirection p := by
  have apex : F.place (C.mateGerm retain p).1.1
      ((C.triangle (C.mateGerm retain p).1.1).vertex (C.mateGerm retain p).1.2) =
      F.place p.1.1 ((C.triangle p.1.1).vertex p.1.2) :=
    congrArg (fun w : C.Vertex retain => F.toSpace retain (C.vertexPoint retain w))
      (C.mateGerm_vertex_eq retain p)
  unfold germDirection
  rw [F.germFarPoint_mate, apex]

theorem face_linear_range_finrank (face : Face) :
    Module.finrank ℝ (LinearMap.range (F.place face).linear) = 2 := by
  have injective : Function.Injective (F.place face).linear :=
    (F.place face).linearIsometry.injective
  rw [LinearMap.finrank_range_of_inj injective]
  norm_num [Plane]

theorem mem_span_germDirection_of_mate_planes (retain : Set C.Seam) (p : C.Germ)
    (different : LinearMap.range (F.place p.1.1).linear ≠
      LinearMap.range (F.place (C.mateGerm retain p).1.1).linear)
    {d : Space} (first : d ∈ LinearMap.range (F.place p.1.1).linear)
    (second : d ∈ LinearMap.range (F.place (C.mateGerm retain p).1.1).linear) :
    d ∈ Submodule.span ℝ {F.germDirection p} := by
  have mate_member : F.germDirection p ∈
      LinearMap.range (F.place (C.mateGerm retain p).1.1).linear := by
    rw [← F.germDirection_mate retain p]
    exact F.germDirection_mem_range _
  have intersection := plane_inf_eq_span (F.face_linear_range_finrank p.1.1)
    (F.face_linear_range_finrank (C.mateGerm retain p).1.1) different
    (F.germDirection_ne_zero p) (F.germDirection_mem_range p) mate_member
  rw [← intersection]
  exact ⟨first, second⟩

end Unfoldings.SpatialFolding
