module

public import Unfoldings.Cap.OriginLeaf
public import Unfoldings.Cap.RoofExtension
public import Unfoldings.Geometry.ConvexRadialTails

/-!
# Disjoint outward radial continuations of the actual original rim roots

From the internal sector origin, extend every original rim root radially
beyond the convex footprint. Different roots have disjoint continuations,
and each continuation lifts canonically to the actual unbounded roof. No
assertion about developing the extension or its extra vertices is made here.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

def projectedRimTail (_M : K.SectorForest t origin) (root : C.Vertex Set.univ) (a : ℝ) : Plane :=
  K.projectedVertex origin + a • (K.projectedVertex root - K.projectedVertex origin)

@[simp] theorem projectedRimTail_one (root : C.Vertex Set.univ) :
    M.projectedRimTail root 1 = K.projectedVertex root := by
  simp only [projectedRimTail, one_smul, add_sub_cancel]

/-- A root's open continuation is entirely outside the original cap footprint. -/
theorem projectedRimTail_outside (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    {root : C.Vertex Set.univ} (boundary : C.IsBoundaryVertex Set.univ root)
    {a : ℝ} (beyond : 1 < a) : M.projectedRimTail root a ∉ K.footprint := by
  exact fun member => radial_tail_not_mem_closure K.convex_projection
    ((K.projectedVertex_mem_interior_iff origin).mpr internal)
    ((K.projectedVertex_mem_frontier_iff root).mpr boundary) beyond (subset_closure member)

/-- Distinct original rim roots cannot acquire a common point on their outward radial tails. -/
theorem projectedRimTail_root_eq (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    {first last : C.Vertex Set.univ}
    (first_boundary : C.IsBoundaryVertex Set.univ first)
    (last_boundary : C.IsBoundaryVertex Set.univ last)
    {a b : ℝ} (a_pos : 0 < a) (b_pos : 0 < b)
    (same : M.projectedRimTail first a = M.projectedRimTail last b) : first = last := by
  apply K.projectedVertex_injective
  exact frontier_eq_of_radial_rays_meet K.convex_projection
    ((K.projectedVertex_mem_interior_iff origin).mpr internal)
    ((K.projectedVertex_mem_frontier_iff first).mpr first_boundary)
    ((K.projectedVertex_mem_frontier_iff last).mpr last_boundary) a_pos b_pos same

/-- The exact continuation on the envelope of the original upward support planes. -/
def spatialRimTail (root : C.Vertex Set.univ) (a : ℝ) : Space :=
  K.roofPoint (M.projectedRimTail root a)

theorem spatialRimTail_mem (root : C.Vertex Set.univ) (a : ℝ) :
    M.spatialRimTail root a ∈ K.extendedRoof := K.roofPoint_mem _

@[simp] theorem spatialRimTail_one (root : C.Vertex Set.univ) :
    M.spatialRimTail root 1 =
      K.folding.toSpace Set.univ (C.vertexPoint Set.univ root) := by
  rw [spatialRimTail, M.projectedRimTail_one, K.roofPoint_projectedVertex]

@[simp] theorem horizontal_spatialRimTail (root : C.Vertex Set.univ) (a : ℝ) :
    Cap.horizontal (M.spatialRimTail root a) = M.projectedRimTail root a :=
  K.horizontal_roofPoint _

theorem continuous_spatialRimTail (root : C.Vertex Set.univ) :
    Continuous (M.spatialRimTail root) := by
  apply K.continuous_roofPoint.comp
  unfold projectedRimTail
  fun_prop

/-- The lifted continuation beyond a root leaves the supplied cap surface. -/
theorem spatialRimTail_outside_surface (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    {root : C.Vertex Set.univ} (boundary : C.IsBoundaryVertex Set.univ root)
    {a : ℝ} (beyond : 1 < a) : M.spatialRimTail root a ∉ K.folding.surface := by
  intro member
  have footprint := ((K.surface_iff_roofHeight _).mp member).1
  rw [M.horizontal_spatialRimTail] at footprint
  exact M.projectedRimTail_outside internal boundary beyond footprint

/-- Every actual tree's radial continuation has a genuine direction in that tree's closed sector. -/
theorem root_radial_direction (nonnegative : 0 ≤ t) (small : t < 1)
    (origin_internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (v : C.Vertex Set.univ) (internal : ¬ C.IsBoundaryVertex Set.univ v) :
    K.projectedVertex (M.parents.root v) - K.projectedVertex origin ∈
        closedThreeSector t (K.sourceSectorLabel t origin v) ∧
      K.projectedVertex (M.parents.root v) - K.projectedVertex origin ≠ 0 := by
  have inside := M.rootPath_position nonnegative small v internal
    (Fin.last (M.parents.distanceToRoot v))
  rw [M.rootPath_end] at inside
  refine ⟨inside, ?_⟩
  intro zero
  have same := K.projectedVertex_injective (sub_eq_zero.mp zero)
  exact origin_internal (same ▸ M.rootPath_end_boundary v)

/-- The lifted tails also retain their distinct original root labels. -/
theorem spatialRimTail_root_eq (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    {first last : C.Vertex Set.univ}
    (first_boundary : C.IsBoundaryVertex Set.univ first)
    (last_boundary : C.IsBoundaryVertex Set.univ last)
    {a b : ℝ} (a_pos : 0 < a) (b_pos : 0 < b)
    (same : M.spatialRimTail first a = M.spatialRimTail last b) : first = last := by
  apply M.projectedRimTail_root_eq internal first_boundary last_boundary a_pos b_pos
  simpa only [M.horizontal_spatialRimTail] using congrArg Cap.horizontal same

end Unfoldings.ConvexCap.SectorForest
