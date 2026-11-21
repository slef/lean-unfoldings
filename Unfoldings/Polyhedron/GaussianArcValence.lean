module

public import Unfoldings.Polyhedron.GaussianArcSupport
public import Unfoldings.Geometry.PlanarExposedRays

/-! At an extreme Gaussian cell, at most two genuine incident sides can meet
at one normal direction. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open Cap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

private theorem openMinorArc_swap (x y : Space) : openMinorArc x y = openMinorArc y x := by
  have inclusion (p q : Space) : openMinorArc p q ⊆ openMinorArc q p := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    rw [sub_sub_cancel, add_comm]
  exact (inclusion x y).antisymm (inclusion y x)

/-- An unoriented dual side has the two listed incident normals as endpoints. -/
def HasGaussianArcEnds (s : C.Seam) (x y : Space) : Prop :=
  (N.normal (C.left s).face = x ∧ N.normal (C.right s).face = y) ∨
    (N.normal (C.left s).face = y ∧ N.normal (C.right s).face = x)

theorem HasGaussianArcEnds.closedMinorArc {s : C.Seam} {x y : Space}
    (h : HasGaussianArcEnds N s x y) :
    closedMinorArc (N.normal (C.left s).face) (N.normal (C.right s).face) =
      closedMinorArc x y := by
  rcases h with ⟨first, last⟩ | ⟨first, last⟩ <;> rw [first, last]
  exact closedMinorArc_comm _ _

theorem HasGaussianArcEnds.openMinorArc {s : C.Seam} {x y : Space}
    (h : HasGaussianArcEnds N s x y) :
    openMinorArc (N.normal (C.left s).face) (N.normal (C.right s).face) = openMinorArc x y := by
  rcases h with ⟨first, last⟩ | ⟨first, last⟩ <;> rw [first, last]
  exact openMinorArc_swap _ _

include P in
/-- Distinct genuine sides at an extreme vertex cannot have the same unordered
pair of normal endpoints. -/
theorem false_of_distinct_seams_with_same_arcEnds
    {a b d : C.Vertex Set.univ} {s t : C.Seam} {x y : Space}
    (extreme : (F.gaussianSiteOfVertex a : Space) ∈ F.vertexHull.extremePoints ℝ)
    (different : s ≠ t) (ls : C.seamGraph.IsLink s a b) (lt : C.seamGraph.IsLink t a d)
    (xy : x ≠ y) (es : HasGaussianArcEnds N s x y) (et : HasGaussianArcEnds N t x y) :
    False := by
  have genuine : N.normal (C.left s).face ≠ N.normal (C.right s).face := by
    rcases es with ⟨l, r⟩ | ⟨l, r⟩ <;> rw [l, r]
    · exact xy
    · exact xy.symm
  have apart := P.disjoint_open_dual_seams_at_extreme_vertex N a b d extreme different ls lt genuine
  rw [es.openMinorArc, et.openMinorArc, disjoint_self] at apart
  have point : (openMinorArc x y).Nonempty :=
    ⟨_, 1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
  exact Set.not_nonempty_empty (apart ▸ point)

include P in
/-- An original incident normal at an extreme vertex has at most two genuine
dual sides through it. The other endpoints are incident face normals. -/
theorem false_of_three_gaussian_arcs_sharing_endpoint
    {a : C.Vertex Set.univ}
    (extreme : (F.gaussianSiteOfVertex a : Space) ∈ F.vertexHull.extremePoints ℝ)
    (seam : Fin 3 → C.Seam) (different : Function.Injective seam)
    (other : Fin 3 → C.Vertex Set.univ) (links : ∀ i, C.seamGraph.IsLink (seam i) a (other i))
    (x : Space) (y : Fin 3 → Space) (genuine : ∀ i, x ≠ y i)
    (endpoints : ∀ i, HasGaussianArcEnds N (seam i) x (y i))
    (at_a : ∀ i, ∃ (f : Face) (j : Fin 3),
      C.vertexOfCorner Set.univ (f, j) = a ∧ N.normal f = y i) :
    False := by
  let cell := F.gaussianCell (F.gaussianSiteOfVertex a)
  have arc_sub (i : Fin 3) : closedMinorArc x (y i) ⊆ cell := by
    rw [← (endpoints i).closedMinorArc]
    have original : F.gaussianCell (F.gaussianSiteOfVertex a) ∩
        F.gaussianCell (F.gaussianSiteOfVertex (other i)) =
          closedMinorArc (N.normal (C.left (seam i)).face) (N.normal (C.right (seam i)).face) := by
      rcases links i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂]
      · exact P.gaussianCell_inter_seam_eq_normal_arc N (seam i)
      · rw [Set.inter_comm]
        exact P.gaussianCell_inter_seam_eq_normal_arc N (seam i)
    rw [← original]
    exact Set.inter_subset_left
  obtain ⟨q, hq, positive⟩ := F.exists_gaussianCell_center P (F.gaussianSiteOfVertex a)
    (F.gaussianCell_nonempty P _)
  let L := northFrame q
  let slope (z : Space) := ((L z) 2)⁻¹ • horizontal (L z)
  have lift (z : Space) (inside : z ∈ cell) : gnomonicNormal (slope z) = L z := by
    apply gnomonicNormal_slope
    · rw [L.norm_map]
      simpa only [Metric.mem_sphere, dist_zero_right] using inside.2
    · have unit : ‖q‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hq.2
      change 0 < northFrame q z 2
      rw [northFrame_height q unit]
      exact positive z inside
  have x_in : x ∈ cell := arc_sub 0 (Set.mem_insert _ _)
  have y_in (i : Fin 3) : y i ∈ cell := arc_sub i (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have y_not_in (i j : Fin 3) (ij : i ≠ j) : y j ∉ closedMinorArc x (y i) := by
    intro present
    rcases Set.mem_insert_iff.mp present with same | in_tail
    · exact genuine j same.symm
    rcases Set.mem_insert_iff.mp in_tail with same | interior
    · exact P.false_of_distinct_seams_with_same_arcEnds N extreme (different.ne ij)
        (links i) (links j) (genuine i) (endpoints i) (same ▸ endpoints j)
    · obtain ⟨f, k, at_corner, normal⟩ := at_a j
      have h := P.face_normal_not_mem_open_dual_arc N (links i) (by
        rcases endpoints i with ⟨l, r⟩ | ⟨l, r⟩ <;> rw [l, r]
        · exact genuine i
        · exact (genuine i).symm) f k at_corner
      apply h
      rwa [(endpoints i).openMinorArc, normal]
  have exposes (i : Fin 3) :
      ∃ f : Plane →ₗ[ℝ] ℝ, f (slope (y i) - slope x) = 0 ∧
        ∀ j, i ≠ j → 0 < f (slope (y j) - slope x) := by
    obtain ⟨f, hf⟩ := P.exists_gnomonicForm_exposing_dual_arc N (links i) q (slope x) (by
      rw [lift x x_in, (endpoints i).closedMinorArc]
      exact Set.mem_image_of_mem _ (Set.mem_insert _ _))
    have member (j : Fin 3) : gnomonicNormal (slope (y j)) ∈ L '' cell := by
      rw [lift _ (y_in j)]
      exact Set.mem_image_of_mem _ (y_in j)
    refine ⟨f, (hf _ (member i)).2.mpr ?_, fun j ij => ?_⟩
    · rw [lift _ (y_in i), (endpoints i).closedMinorArc]
      exact Set.mem_image_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · obtain ⟨nonneg, zero⟩ := hf _ (member j)
      refine lt_of_le_of_ne nonneg (fun eq => y_not_in i j ij ?_)
      have inside := zero.mp eq.symm
      rw [lift _ (y_in j), (endpoints i).closedMinorArc] at inside
      exact L.injective.mem_set_image.mp inside
  obtain ⟨f, f0, fpos⟩ := exposes 0
  obtain ⟨g, g1, gpos⟩ := exposes 1
  obtain ⟨h, h2, hpos⟩ := exposes 2
  exact false_of_three_exposed_planar_rays f0 (fpos 1 (by decide)) (fpos 2 (by decide))
    (gpos 0 (by decide)) g1 (gpos 2 (by decide)) (hpos 0 (by decide)) (hpos 1 (by decide)) h2

end Unfoldings.SpatialFolding.ConvexBoundary
