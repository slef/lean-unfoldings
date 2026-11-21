module

public import Unfoldings.Polyhedron.GaussianChart
public import Unfoldings.Polyhedron.UpperRoofNormalCone
public import Unfoldings.Polyhedron.NormalSelection
public import Unfoldings.Complex.FaceRestrictionVertices

/-! Match the intrinsic vertex classes with the original Gaussian sites. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

theorem toSpace_vertexOfCorner (f : Face) (j : Fin 3) :
    F.toSpace Set.univ (C.vertexPoint Set.univ (C.vertexOfCorner Set.univ (f, j))) =
      F.place f ((C.triangle f).vertex j) := by
  rw [C.vertexPoint_vertexOfCorner]
  rfl

/-- The original physical site of an uncut intrinsic vertex. -/
def gaussianSiteOfVertex (v : C.Vertex Set.univ) : F.hullSites :=
  ⟨F.toSpace Set.univ (C.vertexPoint Set.univ v), by
    obtain ⟨⟨f, j⟩, rfl⟩ := C.vertexOfCorner_surjective Set.univ v
    rw [F.toSpace_vertexOfCorner]
    exact Finset.mem_image.mpr ⟨(f, j), Finset.mem_univ _, rfl⟩⟩

theorem gaussianSiteOfVertex_surjective : Function.Surjective F.gaussianSiteOfVertex := by
  intro i
  obtain ⟨⟨f, j⟩, _, equal⟩ := Finset.mem_image.mp i.property
  refine ⟨C.vertexOfCorner Set.univ (f, j), Subtype.ext ?_⟩
  change F.toSpace Set.univ (C.vertexPoint Set.univ (C.vertexOfCorner Set.univ (f, j))) = i
  rw [F.toSpace_vertexOfCorner]
  exact equal

namespace ConvexBoundary

variable {F} (P : F.ConvexBoundary)

/-- Embeddedness prevents distinct original intrinsic vertices from sharing a Gaussian site. -/
def vertexEquivGaussianSite : C.Vertex Set.univ ≃ F.hullSites :=
  Equiv.ofBijective F.gaussianSiteOfVertex
    ⟨fun _ _ same => C.vertexPoint_injective Set.univ (P.embedded (congrArg Subtype.val same)),
      F.gaussianSiteOfVertex_surjective⟩

end ConvexBoundary

/-- An original triangle normal belongs to the Gaussian cell at each of its corners. -/
theorem normal_mem_gaussianCell_of_corner (N : F.SupportingNormals) (f : Face) (j : Fin 3) :
    N.normal f ∈ F.gaussianCell (F.gaussianSiteOfVertex (C.vertexOfCorner Set.univ (f, j))) := by
  refine ⟨F.mem_gaussianCone_iff.mpr (fun z hz => ?_), ?_⟩
  · change inner ℝ (N.normal f) z ≤ inner ℝ (N.normal f)
      (F.toSpace Set.univ (C.vertexPoint Set.univ (C.vertexOfCorner Set.univ (f, j))))
    rw [F.toSpace_vertexOfCorner]
    have h := N.supporting f z hz
    have on := N.on_plane f ((C.triangle f).vertex j)
    rw [inner_sub_right] at h on
    linarith only [h, on]
  · simpa only [Metric.mem_sphere, dist_zero_right] using N.unit f


namespace ConvexBoundary

variable {F} (P : F.ConvexBoundary) (N : F.SupportingNormals)

open MeasureTheory
open scoped BigOperators ENNReal

set_option maxHeartbeats 1000000 in
-- The two presentations of the restricted complex require dependent type comparison.
include P in
/-- Looking from an interior point towards a vertex includes its complete
original star and puts its projected image in the interior of the roof. -/
theorem exists_upperRoof_with_full_vertex_star (v : C.Vertex Set.univ) :
    ∃ (q : Space) (w : (N.rotate (Cap.northFrame q)).upperComplex.Vertex Set.univ),
      ‖q‖ = 1 ∧ (∀ n ∈ F.gaussianCell (F.gaussianSiteOfVertex v), 0 < inner ℝ q n) ∧
      ¬ (N.rotate (Cap.northFrame q)).upperComplex.IsBoundaryVertex Set.univ w ∧
      (N.rotate (Cap.northFrame q)).upperFolding.toSpace Set.univ
        ((N.rotate (Cap.northFrame q)).upperComplex.vertexPoint Set.univ w) =
          Cap.northFrame q (F.toSpace Set.univ (C.vertexPoint Set.univ v)) ∧
      (N.rotate (Cap.northFrame q)).upperComplex.totalAngle Set.univ w =
        C.totalAngle Set.univ v := by
  classical
  obtain ⟨c, hc⟩ := P.interior_nonempty
  let i := F.gaussianSiteOfVertex v
  let z : Space := i
  let cell := F.gaussianCell i
  have diff : z - c ≠ 0 := by
    obtain ⟨n, hn⟩ := F.gaussianCell_nonempty P (F.gaussianSiteOfVertex v)
    have pos : 0 < inner ℝ (z - c) n := F.inner_pos_of_mem_gaussianCell (i := i) hc hn
    intro zero
    rw [zero, inner_zero_left] at pos
    exact (lt_irrefl _) pos
  let q := NormedSpace.normalize (z - c)
  have q_unit : ‖q‖ = 1 := NormedSpace.norm_normalize diff
  have positive (n : Space) (hn : n ∈ cell) : 0 < inner ℝ q n := by
    change 0 < inner ℝ (NormedSpace.normalize (z - c)) n
    rw [NormedSpace.normalize, real_inner_smul_left]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr diff))
      (F.inner_pos_of_mem_gaussianCell (i := i) hc hn)
  let L := Cap.northFrame q
  let M := N.rotate L
  let U : Set Face := {f | 0 < M.normal f 2}
  let PR := P.rotate L
  let K := PR.upperRoof M
  have full : C.FullStarIn U v := by
    rintro ⟨f, j⟩ same
    have h := F.normal_mem_gaussianCell_of_corner N f j
    rw [same] at h
    change 0 < Cap.northFrame q (N.normal f) 2
    rw [Cap.northFrame_height q q_unit]
    exact positive _ h
  obtain ⟨⟨f, j⟩, at_corner⟩ := C.vertexOfCorner_surjective Set.univ v
  let D := C.restrictFaces U
  let f' : {f : Face // f ∈ U} := ⟨f, full (f, j) at_corner⟩
  let w := D.vertexOfCorner Set.univ (f', j)
  have w_eq : C.includeRestrictedVertexUniv U w = v :=
    (C.includeRestrictedVertex_ofCorner_univ U (f', j)).trans at_corner
  have coordinates (p : D.Vertex Set.univ) :
      M.upperFolding.toSpace Set.univ (D.vertexPoint Set.univ p) =
        L (F.toSpace Set.univ (C.vertexPoint Set.univ (C.includeRestrictedVertexUniv U p))) := by
    obtain ⟨⟨g, k⟩, rfl⟩ := D.vertexOfCorner_surjective Set.univ p
    rw [C.includeRestrictedVertex_ofCorner_univ, F.toSpace_vertexOfCorner]
    have at_corner := M.upperFolding.toSpace_vertexOfCorner (g : M.UpperFace) k
    exact at_corner.trans rfl
  have at_site : M.upperFolding.toSpace Set.univ (D.vertexPoint Set.univ w) = L z := by
    rw [coordinates, w_eq]
    rfl
  have projected : Cap.horizontal (L z) = Cap.horizontal (L c) := by
    have n_form : L (z - c) = ‖z - c‖ • Cap.northLift 0 := by
      calc
        _ = L (‖z - c‖ • q) := by rw [NormedSpace.norm_smul_normalize]
        _ = _ := by rw [map_smul, Cap.northFrame_center q q_unit]
    have h := congrArg Cap.horizontal n_form
    simpa only [map_sub, map_smul, Cap.northLift_horizontal, smul_zero, sub_eq_zero] using h
  have c_inside : L c ∈ interior (F.rotate L).vertexHull := by
    rw [F.rotate_vertexHull]
    have maps : L '' interior F.vertexHull = interior (L '' F.vertexHull) :=
      L.toHomeomorph.image_interior _
    rw [← maps]
    exact Set.mem_image_of_mem _ hc
  have inside : K.projectedVertex w ∈ interior K.footprint := by
    change Cap.horizontal (M.upperFolding.toSpace Set.univ (D.vertexPoint Set.univ w)) ∈
      interior (Cap.horizontal '' M.upperFolding.surface)
    rw [at_site, projected, PR.upperFolding_footprint M]
    exact PR.horizontal_mem_interior_bodyFootprint c_inside
  have w_internal := (K.projectedVertex_mem_interior_iff w).mp inside
  have at_most_one (p : D.Vertex Set.univ) (same : C.includeRestrictedVertexUniv U p = v) :
      p = w := by
    apply D.vertexPoint_injective Set.univ
    apply M.upper_projection_injective PR
    change Cap.horizontal (M.upperFolding.toSpace Set.univ (D.vertexPoint Set.univ p)) =
      Cap.horizontal (M.upperFolding.toSpace Set.univ (D.vertexPoint Set.univ w))
    rw [coordinates, same, at_site]
    rfl
  have angles : (∑ p : D.Vertex Set.univ,
      if C.includeRestrictedVertexUniv U p = v then D.totalAngle Set.univ p else 0) =
        C.regionalCornerSum U (fun c => (C.triangle c.1).cornerAngle c.2) v :=
    C.totalAngle_restricted_vertex_fiber U v
  have sum : (∑ p : D.Vertex Set.univ,
      if C.includeRestrictedVertexUniv U p = v then D.totalAngle Set.univ p else 0) =
        D.totalAngle Set.univ w := by
    rw [Finset.sum_eq_single w]
    · rw [ite_eq_left w_eq]
    · intro p _ ne
      exact ite_eq_right (fun same => ne (at_most_one p same))
    · exact fun h => (h (Finset.mem_univ _)).elim
  rw [sum, C.regionalCornerSum_of_fullStar U _ v full] at angles
  exact ⟨q, w, q_unit, positive, w_internal, at_site, angles⟩

set_option maxHeartbeats 1000000 in
-- Comparing the two spatial cones unfolds the dependent upper-roof coordinates.
include P N in
/-- An upper-roof vertex with the same physical site has exactly the rotated
Gaussian cell when every normal in that cell is upward. -/
theorem sphericalNormalPolygon_eq_image_gaussianCell (v : C.Vertex Set.univ) (q : Space)
    (w : (N.rotate (Cap.northFrame q)).upperComplex.Vertex Set.univ)
    (unit : ‖q‖ = 1)
    (hemisphere : ∀ n ∈ F.gaussianCell (F.gaussianSiteOfVertex v), 0 < inner ℝ q n)
    (internal : ¬ (N.rotate (Cap.northFrame q)).upperComplex.IsBoundaryVertex Set.univ w)
    (site : (N.rotate (Cap.northFrame q)).upperFolding.toSpace Set.univ
      ((N.rotate (Cap.northFrame q)).upperComplex.vertexPoint Set.univ w) =
        Cap.northFrame q (F.toSpace Set.univ (C.vertexPoint Set.univ v))) :
    ((P.rotate (Cap.northFrame q)).upperRoof
      (N.rotate (Cap.northFrame q))).sphericalNormalPolygon w =
      Cap.northFrame q '' F.gaussianCell (F.gaussianSiteOfVertex v) := by
  let L := Cap.northFrame q
  let M := N.rotate L
  let PR := P.rotate L
  let cell := F.gaussianCell (F.gaussianSiteOfVertex v)
  change (PR.upperRoof M).sphericalNormalPolygon w = L '' cell
  rw [PR.upperRoof_sphericalNormalPolygon_eq_body_supports M w internal, site,
    F.rotate_vertexHull]
  ext n
  constructor
  · rintro ⟨n_unit, n_up, support⟩
    let m := L.symm n
    have lm : L m = n := L.apply_symm_apply _
    have local_norm : ‖m‖ = 1 := (L.symm.norm_map n).trans n_unit
    refine ⟨m, ⟨F.mem_gaussianCone_iff.mpr (fun x hx => ?_), ?_⟩, lm⟩
    · have hx' := support (L x) (Set.mem_image_of_mem _ hx)
      rw [← lm, L.inner_map_map, L.inner_map_map] at hx'
      exact hx'
    · simpa only [Metric.mem_sphere, dist_zero_right] using local_norm
  · rintro ⟨m, hm, rfl⟩
    have m_unit : ‖m‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hm.2
    have up : 0 < L m 2 := by
      change 0 < Cap.northFrame q m 2
      rw [Cap.northFrame_height q unit]
      exact hemisphere _ hm
    refine ⟨(L.norm_map m).trans m_unit, up, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [L.inner_map_map, L.inner_map_map]
    exact F.mem_gaussianCone_iff.mp hm.1 x hx

include P N in
/-- The intrinsic angle defect of an actual convex-polyhedron vertex
equals the solid angle of its Gaussian cell, including flat subdivisions. -/
theorem gaussianCell_eq_angular_defect (v : C.Vertex Set.univ) :
    solidAngleMeasure (F.gaussianCell (F.gaussianSiteOfVertex v)) =
      ENNReal.ofReal (2 * Real.pi - C.totalAngle Set.univ v) := by
  obtain ⟨q, w, unit, hemisphere, internal, site, angles⟩ :=
    P.exists_upperRoof_with_full_vertex_star N v
  let L := Cap.northFrame q
  let cell := F.gaussianCell (F.gaussianSiteOfVertex v)
  have equal := P.sphericalNormalPolygon_eq_image_gaussianCell N v q w unit hemisphere internal site
  have same_area := solidAngleMeasure_image L
    (F.isCompact_gaussianCell (F.gaussianSiteOfVertex v)).measurableSet Set.inter_subset_right
  have defect := ((P.rotate L).upperRoof (N.rotate L)).angular_defect_eq_solid_normal w internal
  rw [angles, equal, same_area] at defect
  exact defect.symm

end ConvexBoundary

end Unfoldings.SpatialFolding
