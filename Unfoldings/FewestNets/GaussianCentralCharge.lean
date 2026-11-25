module

public import Unfoldings.FewestNets.SingleCellCyclicCharge
public import Unfoldings.Polyhedron.GaussianBoundaryCycle
public import Unfoldings.Geometry.MinorArcSupportBoundary

/-! Apply central cancellation to the actual original seams of an extreme Gaussian polygon. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets.SingleCellCharge

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)
  {a : C.Vertex Set.univ} {n : ℕ} (c : (C.linkSystem Set.univ a).Chain n)
  (closes : C.linkMate Set.univ a (C.linkTurn Set.univ a c.last) = c.first)
  (covers : ∀ p, c.Visited p)
  {m : ℕ} (count : (cyclicRunStarts (linkNormals N c)).card = m + 1)

local notation "normal" => compressedLinkNormal N c count
local notation "next" => finRotate (m + 1)
local notation "site" => F.gaussianSiteOfVertex a

private theorem gaussianCycle_arc_eq (k : Fin (m + 1)) :
    let s := (P.runStartGaussianSeamEquiv N c closes covers count (next k)).val
    openMinorArc (normal k) (normal (next k)) =
      openMinorArc (N.normal (C.left s).face) (N.normal (C.right s).face) := by
  have ends := P.compressedLinkNormal_arcEnds N c closes covers count (next k)
  dsimp only at ends ⊢
  rw [Equiv.symm_apply_apply] at ends
  rcases ends with ⟨left, right⟩ | ⟨left, right⟩
  · rw [left, right]
  · rw [left, right, openMinorArc_swap]

include P closes covers in
set_option maxHeartbeats 1100000 in
-- The two orders of the compressed original seam endpoints are both allowed.
/-- If membership changes in an extreme Gaussian polygon are witnessed on
one transverse template side, opposite memberships pair the exact charges. -/
theorem gaussian_cycleCharge_pair_of_side_witnesses
    (extreme : (site : Space) ∈ F.vertexHull.extremePoints ℝ)
    (value : Fin (m + 1) → ℝ) (nonzero : ∀ i, value i ≠ 0)
    {x y : Space} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (not_opposite : x + y ≠ 0)
    (transverse : ∀ j : F.hullSites, j ≠ site →
      inner ℝ ((site : Space) - (j : Space)) x ≠ 0 ∨
        inner ℝ ((site : Space) - (j : Space)) y ≠ 0)
    (witness : ∀ i, value i * value (next i) < 0 →
      (openMinorArc (normal i) (normal (next i)) ∩ openMinorArc x y).Nonempty)
    (first second : Fin (m + 1)) :
    cycleCharge (fun i => decide (0 < value i)) first second +
      cycleCharge (fun i => !decide (0 < value i)) first second = 0 := by
  let start := cyclicRunStart (linkNormals N c) count
  let seam := P.runStartGaussianSeamEquiv N c closes covers count
  let edge (i : Fin (m + 1)) := (seam (next i)).val
  have links (i : Fin (m + 1)) : ∃ b, C.seamGraph.IsLink (edge i) a b := by
    obtain ⟨b, link, _⟩ := P.exists_linked_vertex_of_germDirection (c.point (start (next i)))
    exact ⟨b, link⟩
  choose other link using links
  have arc (i : Fin (m + 1)) : openMinorArc (normal i) (normal (next i)) =
      openMinorArc (N.normal (C.left (edge i)).face) (N.normal (C.right (edge i)).face) :=
    P.gaussianCycle_arc_eq N c closes covers count i
  have disjoint : Pairwise fun i j =>
      Disjoint (openMinorArc (normal i) (normal (next i))) (openMinorArc (normal j) (normal (next j))) := by
    intro i j distinct
    rw [arc i, arc j]
    apply P.disjoint_open_dual_seams_at_extreme_vertex N a (other i) (other j) extreme
      ((Subtype.val_injective.comp (seam.injective.comp (finRotate (m + 1)).injective)).ne distinct) (link i) (link j)
    have member : edge i ∈ gaussianArcSeams N a := (seam (next i)).property
    exact (Finset.mem_filter.mp member).2
  let form (j : {b : F.hullSites // b ≠ site}) : Space →ₗ[ℝ] ℝ :=
    (innerSL ℝ ((site : Space) - (j.val : Space))).toLinearMap
  apply cycleCharge_complement_of_sign_changes_le_two value nonzero
  apply card_sign_changes_le_two_of_boundary_witnesses normal value disjoint hx hy not_opposite
    form (fun j => transverse j.val j.property)
  intro i changed
  obtain ⟨z, on_side, on_template⟩ := witness i changed
  have in_both : z ∈ F.gaussianCell site ∩ F.gaussianCell (F.gaussianSiteOfVertex (other i)) := by
    have polygon_eq :
        F.gaussianCell site ∩ F.gaussianCell (F.gaussianSiteOfVertex (other i)) =
          closedMinorArc (N.normal (C.left (edge i)).face) (N.normal (C.right (edge i)).face) := by
      rcases link i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂]
      · exact P.gaussianCell_inter_seam_eq_normal_arc N (edge i)
      · rw [Set.inter_comm]
        exact P.gaussianCell_inter_seam_eq_normal_arc N (edge i)
    rw [polygon_eq]
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ((arc i) ▸ on_side))
  have distinct_sites : F.gaussianSiteOfVertex (other i) ≠ site := by
    intro eq
    have same : (F.gaussianSiteOfVertex (other i) : Space) = (site : Space) :=
      congrArg Subtype.val eq
    rcases link i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂] at same
      exact gaussianSiteOfVertex_seam_ne (F := F) (edge i) same.symm
    · rw [h₁, h₂] at same
      exact gaussianSiteOfVertex_seam_ne (F := F) (edge i) same
  refine ⟨z, on_side, on_template, ?_, ⟨⟨_, distinct_sites⟩, ?_⟩⟩
  · exact fun j => F.mem_gaussianCone_iff_inner_sub.mp in_both.1.1 j.val
  · have first := F.mem_gaussianCone_iff_inner_sub.mp in_both.1.1 (F.gaussianSiteOfVertex (other i))
    have last := F.mem_gaussianCone_iff_inner_sub.mp in_both.2.1 site
    change inner ℝ ((site : Space) - (F.gaussianSiteOfVertex (other i) : Space)) z = 0
    rw [inner_sub_left] at first last ⊢
    linarith only [first, last]

end Unfoldings.SpatialFolding.ConvexBoundary
