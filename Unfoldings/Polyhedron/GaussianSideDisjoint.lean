module

public import Unfoldings.Polyhedron.GaussianSeam
public import Unfoldings.Polyhedron.FaceNormalContact
public import Unfoldings.Complex.RemovedSeamCarrier
public import Unfoldings.Geometry.UnitLine
public import Mathlib.Analysis.Convex.Extreme

/-! Distinct actual dual sides have disjoint interiors at an extreme vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open scoped InnerProductSpace
open Module

private theorem exists_smul_of_common_normals {n m u w : Space}
    (n_unit : ‖n‖ = 1) (m_unit : ‖m‖ = 1) (distinct : n ≠ m) (not_opposite : n + m ≠ 0)
    (u_ne : u ≠ 0) (nu : inner ℝ n u = 0) (mu : inner ℝ m u = 0)
    (nw : inner ℝ n w = 0) (mw : inner ℝ m w = 0) :
    ∃ c : ℝ, c • u = w := by
  have n_ne : n ≠ 0 := by
    intro h
    rw [h, norm_zero] at n_unit
    norm_num at n_unit
  have m_ne : m ≠ 0 := by
    intro h
    rw [h, norm_zero] at m_unit
    norm_num at m_unit
  have independent : LinearIndependent ℝ ![n, m] := by
    apply (LinearIndependent.pair_iff' n_ne).2
    intro c equal
    have collinear : m ∈ Submodule.span ℝ ({n} : Set Space) :=
      Submodule.mem_span_singleton.mpr ⟨c, equal⟩
    rcases inv_norm_smul_eq_or_eq_neg_of_mem_span m_ne n_ne collinear with eq | eq
    · exact distinct (by simpa only [n_unit, m_unit, inv_one, one_smul] using eq)
    · have opposite : n = -m := by simpa only [n_unit, m_unit, inv_one, one_smul] using eq
      exact not_opposite (by rw [opposite, neg_add_cancel])
  let N := Submodule.span ℝ (Set.range ![n, m])
  have rank_N : finrank ℝ N = 2 := by
    simpa only [N, Fintype.card_fin] using finrank_span_eq_card independent
  have rank_O : finrank ℝ Nᗮ = 1 := by
    have total := N.finrank_add_finrank_orthogonal
    rw [rank_N, show finrank ℝ Space = 3 from finrank_euclideanSpace_fin] at total
    omega
  have orthogonal (d : Space) (first : inner ℝ n d = 0) (last : inner ℝ m d = 0) :
      d ∈ Nᗮ := by
    apply (N.mem_orthogonal d).2
    have sub : N ≤ LinearMap.ker (innerSL ℝ d).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · change inner ℝ d n = 0
        rwa [real_inner_comm n d]
      · change inner ℝ d m = 0
        rwa [real_inner_comm m d]
    intro a ha
    have ea : inner ℝ d a = 0 := sub ha
    rwa [real_inner_comm a d] at ea
  obtain ⟨c, equal⟩ := exists_smul_eq_of_finrank_eq_one rank_O
    (x := ⟨u, orthogonal u nu mu⟩) (fun h => u_ne (congrArg Subtype.val h))
    ⟨w, orthogonal w nw mw⟩
  exact ⟨c, congrArg Subtype.val equal⟩

private theorem both_inner_eq_zero_of_openArc {n m p d : Space}
    (n_unit : ‖n‖ = 1) (m_unit : ‖m‖ = 1) (not_opposite : n + m ≠ 0)
    (in_arc : p ∈ openMinorArc n m) (hn : inner ℝ n d ≤ 0) (hm : inner ℝ m d ≤ 0)
    (equal : inner ℝ p d = 0) : inner ℝ n d = 0 ∧ inner ℝ m d = 0 := by
  obtain ⟨t, ht, rfl⟩ := in_arc
  have nonzero := minorArc_chord_ne_zero n_unit m_unit not_opposite ht
  rw [NormedSpace.normalize, real_inner_smul_left, inner_add_left,
    real_inner_smul_left, real_inner_smul_left] at equal
  have sum := (mul_eq_zero.mp equal).resolve_left (inv_ne_zero (norm_ne_zero_iff.mpr nonzero))
  have hn' := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2.le) hn
  have hm' := mul_nonpos_of_nonneg_of_nonpos ht.1.le hm
  have first : (1 - t) * inner ℝ n d = 0 := by linarith only [hn', hm', sum]
  have last : t * inner ℝ m d = 0 := by linarith only [hn', hm', sum]
  exact ⟨(mul_eq_zero.mp first).resolve_left (sub_pos.mpr ht.2).ne',
    (mul_eq_zero.mp last).resolve_left ht.1.ne'⟩

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

private theorem original_site_mem_hull (a : C.Vertex Set.univ) :
    (F.gaussianSiteOfVertex a : Space) ∈ F.vertexHull := by
  rw [F.vertexHull_eq_convexHull_sites]
  exact subset_convexHull ℝ _ (F.gaussianSiteOfVertex a).property

/-- The two physical sites of an original seam are distinct. -/
theorem gaussianSiteOfVertex_seam_ne (s : C.Seam) :
    (F.gaussianSiteOfVertex (C.seamVertex s false) : Space) ≠
      (F.gaussianSiteOfVertex (C.seamVertex s true) : Space) := by
  change F.toSpace Set.univ (C.vertexPoint Set.univ
      (C.vertexOfCorner Set.univ ((C.left s).face, (C.left s).edge))) ≠
    F.toSpace Set.univ (C.vertexPoint Set.univ
      (C.vertexOfCorner Set.univ ((C.left s).face, Triangle.next (C.left s).edge)))
  rw [F.toSpace_vertexOfCorner, F.toSpace_vertexOfCorner]
  exact (F.place (C.left s).face).injective.ne
    ((C.triangle (C.left s).face).edge_endpoints_ne (C.left s).edge)

private theorem original_openSeamImage_eq {s : C.Seam} {a b : C.Vertex Set.univ}
    (link : C.seamGraph.IsLink s a b) :
    F.openSeamImage s = openSegment ℝ (F.gaussianSiteOfVertex a : Space)
      (F.gaussianSiteOfVertex b : Space) := by
  have at_ends :
      F.openSeamImage s = openSegment ℝ (F.gaussianSiteOfVertex (C.seamVertex s false) : Space)
        (F.gaussianSiteOfVertex (C.seamVertex s true) : Space) := by
    unfold openSeamImage
    rfl
  rcases link with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rwa [h₁, h₂]
  · rw [h₁, h₂, openSegment_symm]
    exact at_ends

include P in
private theorem openSeamImage_disjoint_openSeamImage {s t : C.Seam} (different : s ≠ t) :
    Disjoint (F.openSeamImage s) (F.openSeamImage t) := by
  have disjoint := F.openSeamImage_disjoint_removedSeamCarrier P.embedded {s} s
    (Set.mem_singleton s)
  apply disjoint.mono_right
  intro p on_t
  have image :
      F.place (C.left t).face '' openSegment ℝ
          ((C.triangle (C.left t).face).vertex (C.left t).edge)
          ((C.triangle (C.left t).face).vertex (Triangle.next (C.left t).edge)) =
        F.openSeamImage t :=
    image_openSegment ℝ (F.place (C.left t).face).toAffineMap _ _
  rw [← image] at on_t
  obtain ⟨y, hy, rfl⟩ := on_t
  exact F.removed_edge_mem_removedSeamCarrier {s} t (Ne.symm different)
    ⟨y, openSegment_subset_segment ℝ _ _ hy⟩

include P in
private theorem gaussianCell_inter_eq_of_link {e : C.Seam} {v z : C.Vertex Set.univ}
    (link : C.seamGraph.IsLink e v z) :
    F.gaussianCell (F.gaussianSiteOfVertex v) ∩ F.gaussianCell (F.gaussianSiteOfVertex z) =
      closedMinorArc (N.normal (C.left e).face) (N.normal (C.right e).face) := by
  rcases link with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂]
  · exact P.gaussianCell_inter_seam_eq_normal_arc N e
  · rw [Set.inter_comm]
    exact P.gaussianCell_inter_seam_eq_normal_arc N e

include P in
/-- Two different original seams at an extreme vertex have disjoint open dual
arcs when the first seam is a genuine crease. -/
theorem disjoint_open_dual_seams_at_extreme_vertex
    (v u w : C.Vertex Set.univ)
    (extreme : (F.gaussianSiteOfVertex v : Space) ∈ F.vertexHull.extremePoints ℝ)
    {s t : C.Seam} (different : s ≠ t)
    (first : C.seamGraph.IsLink s v u) (last : C.seamGraph.IsLink t v w)
    (crease : N.normal (C.left s).face ≠ N.normal (C.right s).face) :
    Disjoint (openMinorArc (N.normal (C.left s).face) (N.normal (C.right s).face))
      (openMinorArc (N.normal (C.left t).face) (N.normal (C.right t).face)) := by
  let a : Space := F.gaussianSiteOfVertex v
  let b : Space := F.gaussianSiteOfVertex u
  let c : Space := F.gaussianSiteOfVertex w
  let n := N.normal (C.left s).face
  let m := N.normal (C.right s).face
  have ne_end {e : C.Seam} {z : C.Vertex Set.univ} (link : C.seamGraph.IsLink e v z) :
      (F.gaussianSiteOfVertex z : Space) ≠ a := by
    change (F.gaussianSiteOfVertex z : Space) ≠ (F.gaussianSiteOfVertex v : Space)
    rcases link with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂]
    · exact (gaussianSiteOfVertex_seam_ne (F := F) e).symm
    · exact gaussianSiteOfVertex_seam_ne (F := F) e
  have n_support : n ∈ F.gaussianCell (F.gaussianSiteOfVertex v) ∩
      F.gaussianCell (F.gaussianSiteOfVertex u) := by
    rw [P.gaussianCell_inter_eq_of_link N first]
    exact Set.mem_insert _ _
  have m_support : m ∈ F.gaussianCell (F.gaussianSiteOfVertex v) ∩
      F.gaussianCell (F.gaussianSiteOfVertex u) := by
    rw [P.gaussianCell_inter_eq_of_link N first]
    exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have not_opposite : n + m ≠ 0 := by
    obtain ⟨q, _, hemisphere⟩ := F.exists_gaussianCell_center P (F.gaussianSiteOfVertex v)
      (F.gaussianCell_nonempty P _)
    intro zero
    have h := congrArg (fun x : Space => inner ℝ q x) zero
    rw [inner_add_right, inner_zero_right] at h
    exact (add_pos (hemisphere _ n_support.1) (hemisphere _ m_support.1)).ne' h
  have equal_along {z : C.Vertex Set.univ} {p : Space}
      (support : p ∈ F.gaussianCell (F.gaussianSiteOfVertex v) ∩
        F.gaussianCell (F.gaussianSiteOfVertex z)) :
      inner ℝ p ((F.gaussianSiteOfVertex z : Space) - a) = 0 := by
    rw [inner_sub_right, sub_eq_zero]
    exact le_antisymm
      (F.mem_gaussianCone_iff.mp support.1.1 _ (original_site_mem_hull z))
      (F.mem_gaussianCone_iff.mp support.2.1 _ (original_site_mem_hull v))
  apply Set.disjoint_left.mpr
  intro x on_s on_t
  have x_support : x ∈ F.gaussianCell (F.gaussianSiteOfVertex v) ∩
      F.gaussianCell (F.gaussianSiteOfVertex w) := by
    rw [P.gaussianCell_inter_eq_of_link N last]
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ on_t)
  have n_test : inner ℝ n (c - a) ≤ 0 := by
    rw [inner_sub_right, sub_nonpos]
    exact F.mem_gaussianCone_iff.mp n_support.1.1 _ (original_site_mem_hull w)
  have m_test : inner ℝ m (c - a) ≤ 0 := by
    rw [inner_sub_right, sub_nonpos]
    exact F.mem_gaussianCone_iff.mp m_support.1.1 _ (original_site_mem_hull w)
  have orthogonal := both_inner_eq_zero_of_openArc (N.unit _) (N.unit _) not_opposite
    on_s n_test m_test (equal_along x_support)
  obtain ⟨k, parallel⟩ := exists_smul_of_common_normals (N.unit _) (N.unit _) crease
    not_opposite (sub_ne_zero.mpr (ne_end first)) (equal_along n_support)
    (equal_along m_support) orthogonal.1 orthogonal.2
  have k_ne : k ≠ 0 := by
    intro zero
    rw [zero, zero_smul] at parallel
    exact sub_ne_zero.mpr (ne_end last) parallel.symm
  rcases lt_or_gt_of_ne k_ne with negative | positive
  · let α : ℝ := -k / (1 - k)
    let β : ℝ := 1 / (1 - k)
    have denom : 0 < 1 - k := by linarith
    have α_pos : 0 < α := div_pos (neg_pos.mpr negative) denom
    have β_pos : 0 < β := div_pos one_pos denom
    have sum : α + β = 1 := by
      dsimp [α, β]
      field_simp [denom.ne']
      ring
    have coefficient : α + β * k = 0 := by
      dsimp [α, β]
      field_simp [denom.ne']
      ring
    have displacements : α • (b - a) + β • (c - a) = 0 := by
      rw [← parallel, smul_smul, ← add_smul, coefficient, zero_smul]
    have center : α • b + β • c = a := by
      have scalar : α • a + β • a = a := by rw [← add_smul, sum, one_smul]
      rw [smul_sub, smul_sub] at displacements
      calc
        _ = (α • (b - a) + β • (c - a)) + (α • a + β • a) := by
          simp only [smul_sub]; abel
        _ = a := by rw [smul_sub, smul_sub, displacements, scalar, zero_add]
    have on_open : a ∈ openSegment ℝ b c := ⟨α, β, α_pos, β_pos, sum, center⟩
    exact ne_end first (extreme.2 (original_site_mem_hull u) (original_site_mem_hull w) on_open)
  · let β : ℝ := 1 / (2 * (k + 1))
    have denom : 0 < 2 * (k + 1) := by positivity
    have β_pos : 0 < β := div_pos one_pos denom
    have β_small : β < 1 := (div_lt_one denom).2 (by linarith)
    have first_small : β * k < 1 := by
      change (1 / (2 * (k + 1))) * k < 1
      rw [div_mul_eq_mul_div, one_mul, div_lt_one denom]
      linarith
    let point := AffineMap.lineMap a c β
    have on_first : point ∈ openSegment ℝ a b := by
      rw [openSegment_eq_image_lineMap]
      refine ⟨β * k, ⟨mul_pos β_pos positive, first_small⟩, ?_⟩
      dsimp [point]
      rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module', ← parallel, smul_smul]
    have on_last : point ∈ openSegment ℝ a c := by
      rw [openSegment_eq_image_lineMap]
      exact ⟨β, ⟨β_pos, β_small⟩, rfl⟩
    exact Set.disjoint_left.mp (P.openSeamImage_disjoint_openSeamImage different)
      ((original_openSeamImage_eq first).symm ▸ on_first)
      ((original_openSeamImage_eq last).symm ▸ on_last)

include P in
/-- A genuine dual arc contains no incident face normal in its relative
interior. Every original incident face normal on the arc is an endpoint. -/
theorem face_normal_not_mem_open_dual_arc
    {s : C.Seam} {v w : C.Vertex Set.univ} (link : C.seamGraph.IsLink s v w)
    (crease : N.normal (C.left s).face ≠ N.normal (C.right s).face)
    (f : Face) (j : Fin 3) (at_vertex : C.vertexOfCorner Set.univ (f, j) = v) :
    N.normal f ∉ openMinorArc (N.normal (C.left s).face) (N.normal (C.right s).face) := by
  intro on_arc
  let a : Space := F.gaussianSiteOfVertex v
  let l := (C.left s).face
  let r := (C.right s).face
  let n := N.normal l
  let m := N.normal r
  have triangle_normals :
      F.gaussianCell (F.gaussianSiteOfVertex v) ∩ F.gaussianCell (F.gaussianSiteOfVertex w) =
        closedMinorArc n m := P.gaussianCell_inter_eq_of_link N link
  have n_cell : n ∈ F.gaussianCell (F.gaussianSiteOfVertex v) :=
    (show n ∈ F.gaussianCell (F.gaussianSiteOfVertex v) ∩
      F.gaussianCell (F.gaussianSiteOfVertex w) from triangle_normals.symm ▸
        Set.mem_insert _ _).1
  have m_cell : m ∈ F.gaussianCell (F.gaussianSiteOfVertex v) :=
    (show m ∈ F.gaussianCell (F.gaussianSiteOfVertex v) ∩
      F.gaussianCell (F.gaussianSiteOfVertex w) from triangle_normals.symm ▸
        Set.mem_insert_of_mem _ (Set.mem_insert _ _)).1
  have not_opposite : n + m ≠ 0 := by
    obtain ⟨q, _, hemisphere⟩ := F.exists_gaussianCell_center P (F.gaussianSiteOfVertex v)
      (F.gaussianCell_nonempty P _)
    intro zero
    have h := congrArg (fun x : Space => inner ℝ q x) zero
    rw [inner_add_right, inner_zero_right] at h
    exact (add_pos (hemisphere _ n_cell) (hemisphere _ m_cell)).ne' h
  obtain ⟨y, inside⟩ := (C.triangle f).interior_nonempty
  let z := F.place f y
  have in_body : z ∈ F.vertexHull := F.faceImage_subset_vertexHull f
    ⟨_, interior_subset inside, rfl⟩
  have at_a : a = F.place f ((C.triangle f).vertex j) := by
    change F.toSpace Set.univ (C.vertexPoint Set.univ v) = _
    rw [← at_vertex, F.toSpace_vertexOfCorner]
  have equal : inner ℝ (N.normal f) (z - a) = 0 := by
    have level_y := N.on_plane f y
    have level_a := N.on_plane f ((C.triangle f).vertex j)
    rw [at_a, inner_sub_right]
    rw [inner_sub_right] at level_y level_a
    change inner ℝ (N.normal f) (F.place f y) -
      inner ℝ (N.normal f) (F.place f ((C.triangle f).vertex j)) = 0
    linarith only [level_y, level_a]
  have local_level (g : Face) (cell : N.normal g ∈ F.gaussianCell (F.gaussianSiteOfVertex v)) :
      inner ℝ (N.normal g) a = inner ℝ (N.normal g) (F.place g 0) := by
    let x := (C.triangle g).vertex 0
    have body := N.supporting g a (original_site_mem_hull v)
    have face := N.on_plane g x
    have below := F.mem_gaussianCone_iff.mp cell.1 (F.place g x)
      (F.faceImage_subset_vertexHull g ⟨x, (C.triangle g).vertex_mem 0, rfl⟩)
    rw [inner_sub_right] at face body
    exact le_antisymm (sub_nonpos.mp body) ((sub_eq_zero.mp face) ▸ below)
  have nonpos (p : Space) (cell : p ∈ F.gaussianCell (F.gaussianSiteOfVertex v)) :
      inner ℝ p (z - a) ≤ 0 := by
    rw [inner_sub_right, sub_nonpos]
    exact F.mem_gaussianCone_iff.mp cell.1 z in_body
  obtain ⟨left_contact, right_contact⟩ := both_inner_eq_zero_of_openArc (N.unit l) (N.unit r)
    not_opposite on_arc (nonpos _ n_cell) (nonpos _ m_cell) equal
  rw [inner_sub_right, local_level l n_cell] at left_contact
  rw [inner_sub_right, local_level r m_cell] at right_contact
  have left_normal := P.normal_eq_of_interior_contact N l f inside
    (by rw [inner_sub_right]; exact left_contact)
  have right_normal := P.normal_eq_of_interior_contact N r f inside
    (by rw [inner_sub_right]; exact right_contact)
  exact crease (left_normal.trans right_normal.symm)

end Unfoldings.SpatialFolding.ConvexBoundary
