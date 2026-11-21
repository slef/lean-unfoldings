module

public import Unfoldings.Polyhedron.GaussianVertexAngles
public import Unfoldings.Roof.SeamNormalCell
public import Unfoldings.Roof.SphericalPrimalCell
public import Unfoldings.Geometry.GnomonicMinorArc
public import Unfoldings.Geometry.EquatorialMinorArc

/-! The true Gaussian dual of an original seam is its incident-normal minor arc. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

include P in
/-- The Gaussian cells of the two actual seam endpoints meet in the minor
arc between the two incident unit face normals. -/
theorem gaussianCell_inter_seam_eq_normal_arc (s : C.Seam) :
    F.gaussianCell (F.gaussianSiteOfVertex (C.seamVertex s false)) ∩
      F.gaussianCell (F.gaussianSiteOfVertex (C.seamVertex s true)) =
        closedMinorArc (N.normal (C.left s).face) (N.normal (C.right s).face) := by
  let f := (C.left s).face
  let g := (C.right s).face
  let e := (C.left s).edge
  let T := C.triangle f
  let A := F.gaussianSiteOfVertex (C.seamVertex s false)
  let B := F.gaussianSiteOfVertex (C.seamVertex s true)
  have at_A : (A : Space) = F.place f (T.vertex e) :=
    F.toSpace_vertexOfCorner f e
  have at_B : (B : Space) = F.place f (T.vertex (Triangle.next e)) :=
    F.toSpace_vertexOfCorner f (Triangle.next e)
  have A_mem : (A : Space) ∈ F.vertexHull := by
    rw [F.vertexHull_eq_convexHull_sites]
    exact subset_convexHull ℝ _ A.property
  have B_mem : (B : Space) ∈ F.vertexHull := by
    rw [F.vertexHull_eq_convexHull_sites]
    exact subset_convexHull ℝ _ B.property
  let x := (1 / 2 : ℝ) • T.vertex e + (1 / 2 : ℝ) • T.vertex (Triangle.next e)
  have open_edge : x ∈ openSegment ℝ (T.vertex e) (T.vertex (Triangle.next e)) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  let x' : T.Edge e := ⟨x, openSegment_subset_segment ℝ _ _ open_edge⟩
  have nonvertex : ¬ T.IsVertex x := T.not_isVertex_of_mem_openSegment e open_edge
  let z := F.place f x
  have at_z : z = (1 / 2 : ℝ) • (A : Space) + (1 / 2 : ℝ) • (B : Space) := by
    rw [at_A, at_B]
    change (F.place f).toAffineMap
      ((1 / 2 : ℝ) • T.vertex e + (1 / 2 : ℝ) • T.vertex (Triangle.next e)) = _
    rw [Convex.combo_affine_apply (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)]
    rfl
  let S : Set Space := {n | ‖n‖ = 1 ∧ ∀ w ∈ F.vertexHull, inner ℝ n w ≤ inner ℝ n z}
  have midpoint (n : Space) :
      inner ℝ n z = (inner ℝ n (A : Space) + inner ℝ n (B : Space)) / 2 := by
    rw [at_z, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    ring
  have supports_eq : F.gaussianCell A ∩ F.gaussianCell B = S := by
    ext n
    constructor
    · rintro ⟨ha, hb⟩
      refine ⟨by simpa only [Metric.mem_sphere, dist_zero_right] using ha.2, ?_⟩
      intro w hw
      linarith only [F.mem_gaussianCone_iff.mp ha.1 w hw,
        F.mem_gaussianCone_iff.mp hb.1 w hw, midpoint n]
    · rintro ⟨unit, supports⟩
      have at_A := supports A A_mem
      have at_B := supports B B_mem
      have sphere : n ∈ Metric.sphere (0 : Space) 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using unit
      exact ⟨⟨F.mem_gaussianCone_iff.mpr (by
        intro w hw
        linarith only [at_A, at_B, supports w hw, midpoint n]), sphere⟩,
        ⟨F.mem_gaussianCone_iff.mpr (by
        intro w hw
        linarith only [at_A, at_B, supports w hw, midpoint n]), sphere⟩⟩
  have left_support : N.normal f ∈ S := by
    refine ⟨N.unit f, fun w hw => ?_⟩
    have face := N.on_plane f x
    have body := N.supporting f w hw
    rw [inner_sub_right] at face body
    linarith only [face, body]
  have right_support : N.normal g ∈ S := by
    refine ⟨N.unit g, fun w hw => ?_⟩
    have joined : z = F.place g (C.identify s x').val := F.joined s x'
    rw [joined]
    have face := N.on_plane g (C.identify s x').val
    have body := N.supporting g w hw
    rw [inner_sub_right] at face body
    linarith only [face, body]
  obtain ⟨c, hc⟩ := P.interior_nonempty
  have strict (n : Space) (hn : n ∈ S) : 0 < inner ℝ (z - c) n := by
    let functional := innerSL ℝ n
    have nonzero : functional ≠ 0 := by
      intro h
      have value := DFunLike.congr_fun h n
      change inner ℝ n n = 0 at value
      rw [real_inner_self_eq_norm_sq, hn.1] at value
      norm_num at value
    have compare := supporting_functional_lt_on_interior functional nonzero F.vertexHull
      (functional z) hn.2 c hc
    rw [real_inner_comm, inner_sub_right, sub_pos]
    exact compare
  have difference : z - c ≠ 0 := by
    intro zero
    have h := strict _ left_support
    rw [zero, inner_zero_left] at h
    exact (lt_irrefl _) h
  let q := NormedSpace.normalize (z - c)
  let L := Cap.northFrame q
  let M := N.rotate L
  let PR := P.rotate L
  let K := PR.upperRoof M
  have q_unit : ‖q‖ = 1 := NormedSpace.norm_normalize difference
  have upward (n : Space) (hn : n ∈ S) : 0 < L n 2 := by
    change 0 < Cap.northFrame q n 2
    rw [Cap.northFrame_height q q_unit]
    change 0 < inner ℝ (‖z - c‖⁻¹ • (z - c)) n
    rw [real_inner_smul_left]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr difference)) (strict n hn)
  let s' : M.upperComplex.Seam := ⟨s, upward _ left_support, upward _ right_support⟩
  have on_roof : L z ∈ K.folding.surface :=
    Set.mem_iUnion.mpr ⟨(M.upperComplex.left s').face, x, T.edge_subset e x'.property, rfl⟩
  have visible : Cap.horizontal (L z) ∈ interior K.footprint := by
    have horizontal : Cap.horizontal (L z) = Cap.horizontal (L c) := by
      have normal : L (z - c) = ‖z - c‖ • Cap.northLift 0 := by
        calc
          _ = L (‖z - c‖ • q) := by rw [NormedSpace.norm_smul_normalize]
          _ = _ := by rw [map_smul, Cap.northFrame_center q q_unit]
      have comparison := congrArg Cap.horizontal normal
      simpa only [map_sub, map_smul, Cap.northLift_horizontal, smul_zero, sub_eq_zero]
        using comparison
    have c_inside : L c ∈ interior (F.rotate L).vertexHull := by
      rw [F.rotate_vertexHull]
      have images : L '' interior F.vertexHull = interior (L '' F.vertexHull) :=
        L.toHomeomorph.image_interior _
      rw [← images]
      exact Set.mem_image_of_mem _ hc
    change Cap.horizontal (L z) ∈ interior (Cap.horizontal '' M.upperFolding.surface)
    rw [horizontal, PR.upperFolding_footprint M]
    exact PR.horizontal_mem_interior_bodyFootprint c_inside
  have image_support :
      Cap.gnomonicNormal '' K.primalNormalCell (Cap.horizontal (L z)) = L '' S := by
    rw [K.gnomonicImage_primalNormalCell on_roof]
    ext n
    constructor
    · rintro ⟨unit, up, support⟩
      have from_roof := (PR.supports_body_iff_supports_upperFolding M up _).mpr support
      let m := L.symm n
      have Lm : L m = n := L.apply_symm_apply n
      refine ⟨m, ⟨(L.symm.norm_map n).trans unit, ?_⟩, Lm⟩
      intro w hw
      rw [F.rotate_vertexHull] at from_roof
      have bound := from_roof (L w) (Set.mem_image_of_mem _ hw)
      rwa [← Lm, L.inner_map_map, L.inner_map_map] at bound
    · rintro ⟨m, hm, rfl⟩
      refine ⟨(L.norm_map m).trans hm.1, upward _ hm, ?_⟩
      apply (PR.supports_body_iff_supports_upperFolding M (upward _ hm) _).mp
      rw [F.rotate_vertexHull]
      rintro _ ⟨w, hw, rfl⟩
      rw [L.inner_map_map, L.inner_map_map]
      exact hm.2 w hw
  have seam_cell :
      K.primalNormalCell (Cap.horizontal (L z)) =
        segment ℝ (K.normalSlope (M.upperComplex.left s').face)
          (K.normalSlope (M.upperComplex.right s').face) :=
    K.primalNormalCell_eq_segment_on_seam s' x' nonvertex visible
  apply (Set.image_injective.mpr L.injective)
  change L '' (F.gaussianCell A ∩ F.gaussianCell B) =
    L '' closedMinorArc (N.normal f) (N.normal g)
  rw [supports_eq, ← image_support, seam_cell, Cap.gnomonicNormal_image_segment,
    K.gnomonicNormal_normalSlope, K.gnomonicNormal_normalSlope,
    SpatialRotation.image_closedMinorArc_linearIsometry]
  rfl

end Unfoldings.SpatialFolding.ConvexBoundary
