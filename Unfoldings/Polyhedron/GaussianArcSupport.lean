module

public import Unfoldings.Polyhedron.GaussianSideDisjoint
public import Unfoldings.Polyhedron.GaussianOrderedArcs
public import Unfoldings.Cap.Gnomonic

/-! The original dual arc of a seam is an exposed edge in a gnomonic chart. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open Cap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

private theorem gnomonic_support_difference (normal : Space) (x y : Plane)
    (tight : inner ℝ normal (gnomonicNormal x) = 0) :
    inner ℝ (horizontal normal) (y - x) =
      ‖northLift y‖ * inner ℝ normal (gnomonicNormal y) := by
  have pair (z : Plane) :
      ‖northLift z‖ * inner ℝ normal (gnomonicNormal z) =
        inner ℝ (horizontal normal) z + normal 2 := by
    rw [gnomonicNormal, NormedSpace.normalize, real_inner_smul_right,
      ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (northLift_ne_zero z)), one_mul,
      horizontal_inner, northLift_horizontal, northLift_height, mul_one]
  have at_x := pair x
  rw [tight, mul_zero] at at_x
  rw [inner_sub_right, pair y]
  linarith only [at_x]

include P in
/-- A gnomonic support form through a point on a dual side vanishes precisely
on that side, and is nonnegative everywhere else in the normal polygon. -/
theorem exists_gnomonicForm_exposing_dual_arc {s : C.Seam} {a b : C.Vertex Set.univ}
    (link : C.seamGraph.IsLink s a b)
    (q : Space) (x : Plane)
    (on_arc : gnomonicNormal x ∈ northFrame q ''
      closedMinorArc (N.normal (C.left s).face) (N.normal (C.right s).face)) :
    ∃ f : Plane →ₗ[ℝ] ℝ, ∀ y : Plane,
      gnomonicNormal y ∈ northFrame q '' F.gaussianCell (F.gaussianSiteOfVertex a) →
      0 ≤ f (y - x) ∧
        (f (y - x) = 0 ↔ gnomonicNormal y ∈ northFrame q ''
          closedMinorArc (N.normal (C.left s).face) (N.normal (C.right s).face)) := by
  let L := northFrame q
  let ai := F.gaussianSiteOfVertex a
  let bi := F.gaussianSiteOfVertex b
  let inward := L ((ai : Space) - bi.val)
  have cell_arc : F.gaussianCell ai ∩ F.gaussianCell bi =
      closedMinorArc (N.normal (C.left s).face) (N.normal (C.right s).face) := by
    change F.gaussianCell (F.gaussianSiteOfVertex a) ∩ F.gaussianCell (F.gaussianSiteOfVertex b) = _
    rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact P.gaussianCell_inter_seam_eq_normal_arc N s
    · rw [Set.inter_comm]
      exact P.gaussianCell_inter_seam_eq_normal_arc N s
  have support_eq (z : Space) (inside : z ∈ F.gaussianCell ai) :
      inner ℝ ((ai : Space) - bi.val) z = 0 ↔
        z ∈ closedMinorArc (N.normal (C.left s).face) (N.normal (C.right s).face) := by
    rw [← cell_arc]
    refine ⟨fun h => ⟨inside, ?_⟩, fun h => ?_⟩
    · refine ⟨(F.mem_gaussianCone_iff_inner_sub).mpr fun j => ?_, inside.2⟩
      have le := (F.mem_gaussianCone_iff_inner_sub).mp inside.1 j
      have decomp : ((bi : Space) - (j : Space)) =
          ((ai : Space) - (j : Space)) - ((ai : Space) - bi.val) := by abel
      rwa [decomp, inner_sub_left, h, sub_zero]
    · have a_le := (F.mem_gaussianCone_iff_inner_sub).mp inside.1 bi
      have b_le := (F.mem_gaussianCone_iff_inner_sub).mp h.2.1 ai
      rw [show (bi : Space) - ai.val = -((ai : Space) - bi.val) by abel,
        inner_neg_left] at b_le
      linarith
  have transport (z : Space) :
      inner ℝ inward (L z) = inner ℝ ((ai : Space) - bi.val) z := L.inner_map_map _ _
  have tight : inner ℝ inward (gnomonicNormal x) = 0 := by
    obtain ⟨z, hz, eq⟩ := on_arc
    rw [← eq, transport]
    exact (support_eq z ((cell_arc.symm ▸ hz).1)).mpr hz
  refine ⟨(innerSL ℝ (horizontal inward)).toLinearMap, ?_⟩
  intro y inside
  obtain ⟨z, hz, eq⟩ := inside
  change 0 ≤ inner ℝ (horizontal inward) (y - x) ∧
    (inner ℝ (horizontal inward) (y - x) = 0 ↔ _)
  rw [gnomonic_support_difference inward x y tight, ← eq, transport]
  have norm_pos := norm_pos_iff.mpr (northLift_ne_zero y)
  refine ⟨mul_nonneg norm_pos.le ((F.mem_gaussianCone_iff_inner_sub).mp hz.1 bi), ?_⟩
  rw [mul_eq_zero, or_iff_right norm_pos.ne', support_eq z hz]
  exact L.injective.mem_set_image.symm

end Unfoldings.SpatialFolding.ConvexBoundary
