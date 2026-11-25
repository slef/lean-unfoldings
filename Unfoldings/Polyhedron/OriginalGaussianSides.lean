module

public import Unfoldings.Polyhedron.GaussianOrderedArcs
public import Unfoldings.Polyhedron.GaussianSideDisjoint
public import Unfoldings.Polyhedron.GaussianExtremeCells
public import Unfoldings.Geometry.SphericalConvex

/-! The genuine sides at an original vertex lie on the actual Gaussian support planes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open InnerProductGeometry

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

variable (a : C.Vertex Set.univ)

local notation "site" => F.gaussianSiteOfVertex a
local notation "cell" => F.gaussianCell site

/-- The constraint corresponding to another physical site of the original hull. -/
def gaussianWallForm (w : {w : F.hullSites // w ≠ site}) : Space →ₗ[ℝ] ℝ :=
  (innerSL ℝ ((site : Space) - (w.val : Space))).toLinearMap

theorem gaussianWallForm_ne_zero (w : {w : F.hullSites // w ≠ site}) :
    gaussianWallForm (F := F) a w ≠ 0 := by
  intro zero
  have eq := DFunLike.congr_fun zero ((site : Space) - (w.val : Space))
  change inner ℝ ((site : Space) - (w.val : Space)) ((site : Space) - (w.val : Space)) = 0 at eq
  exact w.property (Subtype.ext (sub_eq_zero.mp (inner_self_eq_zero.mp eq)).symm)

theorem mem_gaussianCell_iff_wall (x : Space) :
    x ∈ cell ↔ ‖x‖ = 1 ∧ ∀ w, 0 ≤ gaussianWallForm (F := F) a w x := by
  constructor
  · intro inside
    have u : ‖x‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using inside.2
    exact ⟨u, fun w => (F.mem_gaussianCone_iff_inner_sub.mp inside.1) w.val⟩
  · rintro ⟨unit, support⟩
    refine ⟨F.mem_gaussianCone_iff_inner_sub.mpr (fun w => ?_),
      Metric.mem_sphere.mpr ((dist_zero_right _).trans unit)⟩
    by_cases equal : w = site
    · subst w
      simp
    · exact support ⟨w, equal⟩


/-- The actual Gaussian cell contains normalized positive combinations. -/
theorem sphericalConvex_original_gaussianCell : SphericalConvex cell := by
  refine ⟨fun x hx => ((mem_gaussianCell_iff_wall (F := F) a x).mp hx).1, ?_⟩
  intro x hx y hy c d hc hd nonzero
  apply (mem_gaussianCell_iff_wall (F := F) a _).mpr
  refine ⟨NormedSpace.norm_normalize nonzero, fun w => ?_⟩
  have first := ((mem_gaussianCell_iff_wall (F := F) a x).mp hx).2 w
  have last := ((mem_gaussianCell_iff_wall (F := F) a y).mp hy).2 w
  rw [NormedSpace.normalize, map_smul, map_add, map_smul, map_smul]
  exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
    (add_nonneg (mul_nonneg hc first) (mul_nonneg hd last))

private theorem exists_seam_link_of_incident {s : C.Seam} (member : s ∈ incidentSeams a) :
    ∃ b, C.seamGraph.IsLink s a b := by
  classical
  rcases (Finset.mem_filter.mp member).2 with left | right
  · exact ⟨C.seamVertex s true, Or.inl ⟨left, rfl⟩⟩
  · exact ⟨C.seamVertex s false, Or.inr ⟨right, rfl⟩⟩

include P in
/-- One actual wall supports the entire minor arc of an incident seam. -/
theorem exists_gaussianWallForm_eq_zero_on_arc {s : C.Seam} (member : s ∈ incidentSeams a) :
    ∃ w : {w : F.hullSites // w ≠ site}, ∀ x ∈ closedMinorArc (N.normal (C.left s).face) (N.normal (C.right s).face),
      x ∈ cell ∧ gaussianWallForm (F := F) a w x = 0 := by
  obtain ⟨b, link⟩ := exists_seam_link_of_incident a member
  have distinct : F.gaussianSiteOfVertex b ≠ site := by
    intro same
    change F.gaussianSiteOfVertex b = F.gaussianSiteOfVertex a at same
    have equal := congrArg (fun w : F.hullSites => (w : Space)) same
    rcases link with ⟨left, right⟩ | ⟨left, right⟩ <;> rw [left, right] at equal
    · exact gaussianSiteOfVertex_seam_ne (F := F) s equal.symm
    · exact gaussianSiteOfVertex_seam_ne (F := F) s equal
  have intersection : cell ∩ F.gaussianCell (F.gaussianSiteOfVertex b) =
      closedMinorArc (N.normal (C.left s).face) (N.normal (C.right s).face) := by
    rcases link with ⟨left, right⟩ | ⟨left, right⟩ <;> rw [left, right]
    · exact P.gaussianCell_inter_seam_eq_normal_arc N s
    · rw [Set.inter_comm]
      exact P.gaussianCell_inter_seam_eq_normal_arc N s
  refine ⟨⟨F.gaussianSiteOfVertex b, distinct⟩, fun x hx => ?_⟩
  have both := intersection.symm ▸ hx
  refine ⟨both.1, ?_⟩
  have from_a := F.mem_gaussianCone_iff_inner_sub.mp both.1.1 (F.gaussianSiteOfVertex b)
  have from_b := F.mem_gaussianCone_iff_inner_sub.mp both.2.1 site
  change inner ℝ ((site : Space) - (F.gaussianSiteOfVertex b : Space)) x = 0
  rw [inner_sub_left] at from_a from_b ⊢
  linarith only [from_a, from_b]

include P in
/-- The whole side belongs to the Gaussian cell and its endpoints are nonantipodal. -/
theorem gaussianSide_nonantipodal {s : C.Seam} (member : s ∈ incidentSeams a) :
    N.normal (C.left s).face + N.normal (C.right s).face ≠ 0 := by
  obtain ⟨w, supported⟩ := P.exists_gaussianWallForm_eq_zero_on_arc N a member
  have left := (supported _ (Set.mem_insert _ _)).1
  have right := (supported _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))).1
  obtain ⟨q, _, hemisphere⟩ := F.exists_gaussianCell_center P site (F.gaussianCell_nonempty P site)
  intro zero
  have sum := congrArg (fun z : Space => inner ℝ q z) zero
  rw [inner_add_right, inner_zero_right] at sum
  exact (add_pos (hemisphere _ left) (hemisphere _ right)).ne' sum

include P in
/-- Different genuine original sides of an extreme cell have disjoint open arcs. -/
theorem pairwise_disjoint_genuine_gaussianSides
    (extreme : (site : Space) ∈ F.vertexHull.extremePoints ℝ) :
    Pairwise fun s t : (gaussianArcSeams N a : Set C.Seam) =>
      Disjoint (openMinorArc (N.normal (C.left s.val).face) (N.normal (C.right s.val).face))
        (openMinorArc (N.normal (C.left t.val).face) (N.normal (C.right t.val).face)) := by
  intro s t different
  obtain ⟨b, first⟩ := exists_seam_link_of_incident a (Finset.mem_filter.mp s.property).1
  obtain ⟨c, last⟩ := exists_seam_link_of_incident a (Finset.mem_filter.mp t.property).1
  exact P.disjoint_open_dual_seams_at_extreme_vertex N a b c extreme
    (Subtype.val_injective.ne different) first last (Finset.mem_filter.mp s.property).2

end Unfoldings.SpatialFolding.ConvexBoundary
