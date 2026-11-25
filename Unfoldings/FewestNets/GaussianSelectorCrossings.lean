module

public import Unfoldings.FewestNets.SphericalSelectorPlacement
public import Unfoldings.Geometry.MinorArcSupportBoundary
public import Unfoldings.Polyhedron.OriginalGaussianSides

/-! Almost every placement gives an open crossing for each changed original seam. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open SpatialRotation MeasureTheory

/-- Evaluate a fixed original direction against the moving spherical selector. -/
def movedSiteFlag (region : Set Space) (b : Bool) (g : SpatialRotation) (x : Space) : Bool :=
  siteFlag region b x g⁻¹

@[simp] theorem movedSiteFlag_eq_true_iff (region : Set Space) (b : Bool)
    (g : SpatialRotation) (x : Space) :
    movedSiteFlag region b g x = true ↔ x ∈ orthogonalIsometry g b '' region := by
  let T := orthogonalIsometry g b
  rw [movedSiteFlag, siteFlag_eq_true_iff, ← orthogonalIsometry_apply, ← orthogonalIsometry_symm]
  change T.symm x ∈ region ↔ x ∈ T '' region
  constructor
  · exact fun inside => ⟨T.symm x, inside, T.apply_symm_apply x⟩
  · rintro ⟨v, hv, rfl⟩
    rwa [T.symm_apply_apply]

end Unfoldings.FewestNets

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets SpatialRotation MeasureTheory

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)
  {J : Type*} [Finite J] {region : Set Space} (B : SphericalSelectorBoundary J region)
  (a : C.Vertex Set.univ)

local notation "site" => F.gaussianSiteOfVertex a
local notation "cell" => F.gaussianCell site

/-- All placed template vertices avoid the original Gaussian support planes. -/
theorem ae_selector_endpoints_avoid_gaussian_walls (b : Bool) :
    ∀ᵐ g ∂probability, ∀ j k (w : {w : F.hullSites // w ≠ site}),
      gaussianWallForm (F := F) a w (orthogonalIsometry g b (B.endpoint j k)) ≠ 0 := by
  have h := ae_orthogonalIsometry_avoids_hyperplanes b
    (fun p : J × Bool => B.endpoint p.1 p.2) (fun p => B.endpoint_unit p.1 p.2)
    (gaussianWallForm (F := F) a) (gaussianWallForm_ne_zero (F := F) a)
  exact h.mono fun g hg j k w => hg (j, k) w

include P in
set_option maxHeartbeats 1000000 in
/-- Every changed side has an intersection in the open interiors of its
original Gaussian arc and a genuine placed selector side. -/
theorem ae_gaussian_selector_crossing (b : Bool) :
    ∀ᵐ g ∂probability, ∀ s ∈ incidentSeams a,
      movedSiteFlag region b g (N.normal (C.left s).face) ≠
        movedSiteFlag region b g (N.normal (C.right s).face) →
    ∃ j x, x ∈ openMinorArc (N.normal (C.left s).face) (N.normal (C.right s).face) ∧
      x ∈ openMinorArc (orthogonalIsometry g b (B.endpoint j false))
        (orthogonalIsometry g b (B.endpoint j true)) ∧ x ∈ cell := by
  have normals_generic := ae_orthogonalIsometry_symm_avoids_hyperplanes b N.normal N.unit
    B.form B.form_ne_zero
  filter_upwards [normals_generic, ae_selector_endpoints_avoid_gaussian_walls B a b] with
    g face_off vertices_off s at_a changed
  let T := orthogonalIsometry g b
  let placed := B.map T
  let u := N.normal (C.left s).face
  let v := N.normal (C.right s).face
  have membership (f : Face) :
      movedSiteFlag region b g (N.normal f) = true ↔ ∀ j, 0 ≤ placed.form j (N.normal f) := by
    rw [movedSiteFlag_eq_true_iff, placed.membership, and_iff_right (N.unit f)]
  have opposite : ¬ ((∀ j, 0 ≤ placed.form j u) ↔ (∀ j, 0 ≤ placed.form j v)) := by
    rw [← membership (C.left s).face, ← membership (C.right s).face]
    intro agree
    have equal_of_true_iff {p q : Bool} (iff_true : p = true ↔ q = true) : p = q := by
      cases p <;> cases q <;> first | rfl | simp at iff_true
    exact changed (equal_of_true_iff agree)
  obtain ⟨j, x, on_seam, on_side⟩ := exists_openMinorArc_inter_selector_side placed.form
    (networkEdge placed.endpoint) (N.unit _) (N.unit _) (P.gaussianSide_nonantipodal N a at_a)
    (face_off (C.left s).face) (face_off (C.right s).face) opposite
    (fun x unit support k zero => placed.side_mem.mpr
      ⟨(placed.membership x).mpr ⟨by simpa only [Metric.mem_sphere, dist_zero_right] using unit,
        support⟩, zero⟩)
  obtain ⟨w, contact⟩ := P.exists_gaussianWallForm_eq_zero_on_arc N a at_a
  have on_wall := contact x (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ on_seam))
  change x ∈ closedMinorArc (T (B.endpoint j false)) (T (B.endpoint j true)) at on_side
  rcases Set.mem_insert_iff.mp on_side with same | on_side
  · exact (vertices_off j false w (same ▸ on_wall.2)).elim
  rcases Set.mem_insert_iff.mp on_side with same | open_side
  · exact (vertices_off j true w (same ▸ on_wall.2)).elim
  exact ⟨j, x, on_seam, open_side, on_wall.1⟩

end Unfoldings.SpatialFolding.ConvexBoundary
