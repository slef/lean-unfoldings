module

public import Unfoldings.Roof.SectorForestGeometry
public import Unfoldings.Roof.Boundary
public import Unfoldings.Geometry.ConvexRadialTails

/-! Original rim continuations from an interior planar source, without a rim-height assumption. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)

def projectedRimTail (_M : K.SectorForest t origin) (root : C.Vertex Set.univ) (a : ℝ) : Plane :=
  origin + a • (K.projectedVertex root - origin)

@[simp] theorem projectedRimTail_one (root : C.Vertex Set.univ) :
    M.projectedRimTail root 1 = K.projectedVertex root := by
  simp only [projectedRimTail, one_smul, add_sub_cancel]

theorem projectedRimTail_outside {root : C.Vertex Set.univ}
    (boundary : C.IsBoundaryVertex Set.univ root) {a : ℝ} (beyond : 1 < a) :
    M.projectedRimTail root a ∉ K.footprint := by
  exact fun member => radial_tail_not_mem_closure K.convex_projection M.inside
    ((K.projectedVertex_mem_frontier_iff root).mpr boundary) beyond (subset_closure member)

theorem projectedRimTail_root_eq {first last : C.Vertex Set.univ}
    (first_boundary : C.IsBoundaryVertex Set.univ first)
    (last_boundary : C.IsBoundaryVertex Set.univ last)
    {a b : ℝ} (a_pos : 0 < a) (b_pos : 0 < b)
    (same : M.projectedRimTail first a = M.projectedRimTail last b) : first = last := by
  apply K.projectedVertex_injective
  exact frontier_eq_of_radial_rays_meet K.convex_projection M.inside
    ((K.projectedVertex_mem_frontier_iff first).mpr first_boundary)
    ((K.projectedVertex_mem_frontier_iff last).mpr last_boundary) a_pos b_pos same

theorem root_radial_direction (nonnegative : 0 ≤ t) (small : t < 1)
    (v : C.Vertex Set.univ) (internal : ¬ C.IsBoundaryVertex Set.univ v) :
    K.projectedVertex (M.parents.root v) - origin ∈
        closedThreeSector t (K.sourceSectorLabel t origin v) ∧
      K.projectedVertex (M.parents.root v) - origin ≠ 0 := by
  have inside := M.rootPath_position nonnegative small v internal
    (Fin.last (M.parents.distanceToRoot v))
  rw [M.rootPath_end] at inside
  refine ⟨inside, ?_⟩
  intro zero
  have same := sub_eq_zero.mp zero
  have boundary := (K.projectedVertex_mem_frontier_iff _).mpr (M.rootPath_end_boundary v)
  exact boundary.2 (same.symm ▸ M.inside)

end Unfoldings.ConvexRoof.SectorForest
