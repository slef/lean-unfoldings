module

public import Unfoldings.Roof.GermNormalCone
public import Unfoldings.Roof.SeamNormalCell
public import Unfoldings.Polyhedron.GaussianVertexAngles

/-! The actual incident directions give all support lines of the gnomonic normal polygon. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {v : C.Vertex Set.univ}

/-- In slope coordinates, the linear normal test along an actual incident edge. -/
def normalGermForm (p : C.LinkGerm Set.univ v) (g : Plane) : ℝ :=
  inner ℝ g (Cap.horizontal (K.folding.germDirection p.val)) + K.folding.germDirection p.val 2

theorem mem_normalPolygon_iff_germ_forms_nonpos
    (inside : K.projectedVertex v ∈ interior K.footprint) (g : Plane) :
    g ∈ K.normalPolygon v ↔ ∀ p : C.LinkGerm Set.univ v, K.normalGermForm p g ≤ 0 := by
  let n := Cap.gnomonicNormal g
  have up : 0 < n 2 := Cap.gnomonicNormal_upward g
  have unit : ‖n‖ = 1 := Cap.gnomonicNormal_unit g
  have image : g ∈ K.normalPolygon v ↔ n ∈ K.sphericalNormalPolygon v :=
    (Cap.gnomonicNormal_injective.mem_set_image).symm
  rw [image, K.mem_sphericalNormalPolygon_iff_germs_nonpos inside n unit up]
  have slope : (n 2)⁻¹ • Cap.horizontal n = g := Cap.slope_gnomonicNormal g
  have form (p : C.LinkGerm Set.univ v) :
      K.normalGermForm p g = (n 2)⁻¹ * inner ℝ n (K.folding.germDirection p.val) := by
    unfold normalGermForm
    rw [← slope, real_inner_smul_left, Cap.horizontal_inner, mul_add, ← mul_assoc,
      inv_mul_cancel₀ up.ne', one_mul]
  constructor
  · intro nonpos p
    rw [form]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr up.le) (nonpos p)
  · intro nonpos p
    have h := nonpos p
    rw [form] at h
    exact nonpos_of_mul_nonpos_right h (inv_pos.mpr up)

/-- Every boundary point of the normal polygon lies on a support line of an
actual incident edge. -/
theorem exists_germ_form_eq_zero_of_mem_frontier
    (inside : K.projectedVertex v ∈ interior K.footprint)
    {g : Plane} (on_frontier : g ∈ frontier (K.normalPolygon v)) :
    ∃ p : C.LinkGerm Set.univ v, K.normalGermForm p g = 0 := by
  have closed := (K.compact_normalPolygon v).isClosed
  rw [closed.frontier_eq] at on_frontier
  have nonpos := (K.mem_normalPolygon_iff_germ_forms_nonpos inside g).mp on_frontier.1
  by_contra! no_zero
  let U := ⋂ p : C.LinkGerm Set.univ v, {h : Plane | K.normalGermForm p h < 0}
  have open_U : IsOpen U := isOpen_iInter_of_finite fun p => isOpen_lt
    ((continuous_id.inner continuous_const).add continuous_const) continuous_const
  have g_in : g ∈ U := Set.mem_iInter.mpr fun p => lt_of_le_of_ne (nonpos p) (no_zero p)
  have subset : U ⊆ K.normalPolygon v := by
    intro h hh
    exact (K.mem_normalPolygon_iff_germ_forms_nonpos inside h).mpr
      (fun p => (show K.normalGermForm p h < 0 from Set.mem_iInter.mp hh p).le)
  exact on_frontier.2 (interior_maximal subset open_U g_in)

theorem normalPolygon_eq_primalNormalCell
    (inside : K.projectedVertex v ∈ interior K.footprint) :
    K.normalPolygon v = K.primalNormalCell (K.projectedVertex v) := by
  ext g
  rw [K.mem_normalPolygon_iff_supports_footprint v inside g]
  constructor
  · intro support x hx
    have bound := support x hx
    rw [inner_sub_right, real_inner_comm x g, real_inner_comm (K.projectedVertex v) g] at bound
    change inner ℝ x g - inner ℝ (K.projectedVertex v) g ≤
      -K.roofHeight x + K.roofHeight (K.projectedVertex v)
    linarith only [bound]
  · intro support x hx
    have bound := support x hx
    rw [inner_sub_right, real_inner_comm x g, real_inner_comm (K.projectedVertex v) g]
    linarith only [bound]

/-- The face of the normal polygon on an incident edge's support line consists
of the normal slopes supporting both endpoints of that edge. -/
theorem normalPolygon_germSection_eq_inter
    (inside : K.projectedVertex v ∈ interior K.footprint) (p : C.LinkGerm Set.univ v) :
    K.normalPolygon v ∩ {g | K.normalGermForm p g = 0} =
      K.primalNormalCell (K.projectedVertex v) ∩
        K.primalNormalCell
          (K.projectedVertex (C.vertexOfCorner Set.univ (C.germFarCorner p.val))) := by
  let w := C.vertexOfCorner Set.univ (C.germFarCorner p.val)
  let z₀ := K.folding.toSpace Set.univ (C.vertexPoint Set.univ v)
  let z₁ := K.folding.toSpace Set.univ (C.vertexPoint Set.univ w)
  have roof₀ : z₀ ∈ K.folding.surface := (K.folding.range_toSpace Set.univ).subset ⟨_, rfl⟩
  have roof₁ : z₁ ∈ K.folding.surface := (K.folding.range_toSpace Set.univ).subset ⟨_, rfl⟩
  have at₀ := (K.surface_iff_roofHeight z₀).mp roof₀
  have at₁ := (K.surface_iff_roofHeight z₁).mp roof₁
  have dir : K.folding.germDirection p.val = z₁ - z₀ := by
    rw [SpatialFolding.germDirection, K.folding.linkGerm_apex Set.univ v p]
    have far := K.folding.toSpace_vertexOfCorner (C.germFarCorner p.val).1
      (C.germFarCorner p.val).2
    exact congrArg (fun z : Space => z - z₀) far.symm
  have formula (g : Plane) :
      K.normalGermForm p g =
        (inner ℝ (K.projectedVertex w) g + K.roofHeight (K.projectedVertex w)) -
        (inner ℝ (K.projectedVertex v) g + K.roofHeight (K.projectedVertex v)) := by
    rw [normalGermForm, dir, map_sub, inner_sub_right]
    change inner ℝ g (Cap.horizontal z₁) - inner ℝ g (Cap.horizontal z₀) + (z₁ 2 - z₀ 2) =
      (inner ℝ (Cap.horizontal z₁) g + K.roofHeight (Cap.horizontal z₁)) -
      (inner ℝ (Cap.horizontal z₀) g + K.roofHeight (Cap.horizontal z₀))
    rw [at₀.2, at₁.2, real_inner_comm (Cap.horizontal z₀) g, real_inner_comm (Cap.horizontal z₁) g]
    ring
  rw [K.normalPolygon_eq_primalNormalCell inside]
  ext g
  change (g ∈ K.primalNormalCell (K.projectedVertex v) ∧ K.normalGermForm p g = 0) ↔
    (g ∈ K.primalNormalCell (K.projectedVertex v) ∧ g ∈ K.primalNormalCell (K.projectedVertex w))
  have mem₀ : K.projectedVertex v ∈ K.footprint := at₀.1
  have mem₁ : K.projectedVertex w ∈ K.footprint := at₁.1
  simp only [K.primalNormalCell_iff_dual mem₀ g, K.primalNormalCell_iff_dual mem₁ g, formula]
  exact and_congr_right fun h => by rw [h, sub_eq_zero]; exact eq_comm

theorem exists_seam_link_of_germ_at_interior
    (inside : K.projectedVertex v ∈ interior K.footprint) (p : C.LinkGerm Set.univ v) :
    ∃ s : C.Seam, C.seamGraph.IsLink s v
      (C.vertexOfCorner Set.univ (C.germFarCorner p.val)) := by
  have internal := (K.projectedVertex_mem_interior_iff v).mp inside
  have moved : C.mateGerm Set.univ p.val ≠ p.val := by
    intro fixed
    exact internal ((C.isBoundaryVertex_iff_linkMate_fixed Set.univ v).mpr
      ⟨p, Subtype.ext fixed⟩)
  obtain ⟨s, _, side, flag, source, _⟩ := C.germCrosses_mate_of_ne Set.univ p.val moved
  have apex : C.vertexOfCorner Set.univ (C.germOfEndpoint (C.seamSide s side) flag).1 = v := by
    rw [← source]
    exact p.property
  have link : C.seamGraph.IsLink s
      (C.vertexOfCorner Set.univ (C.germOfEndpoint (C.seamSide s side) flag).1)
      (C.vertexOfCorner Set.univ
        (C.germFarCorner (C.germOfEndpoint (C.seamSide s side) flag))) := by
    rw [C.germFarCorner_germOfEndpoint]
    cases flag
    · exact C.seamGraph_side_link s side
    · exact (C.seamGraph_side_link s side).symm
  rw [apex, ← source] at link
  exact ⟨s, link⟩

/-- The boundary of an interior roof vertex's gnomonic normal polygon is
covered by the dual segments of actual seams incident to the vertex. -/
theorem exists_seam_slope_segment_of_mem_normalPolygon_frontier
    (inside : K.projectedVertex v ∈ interior K.footprint) {g : Plane}
    (on_frontier : g ∈ frontier (K.normalPolygon v)) :
    ∃ (s : C.Seam) (w : C.Vertex Set.univ), C.seamGraph.IsLink s v w ∧
      g ∈ segment ℝ (K.normalSlope (C.left s).face) (K.normalSlope (C.right s).face) := by
  obtain ⟨p, tight⟩ := K.exists_germ_form_eq_zero_of_mem_frontier inside on_frontier
  obtain ⟨s, link⟩ := K.exists_seam_link_of_germ_at_interior inside p
  let w := C.vertexOfCorner Set.univ (C.germFarCorner p.val)
  refine ⟨s, w, link, ?_⟩
  have section_eq := K.normalPolygon_germSection_eq_inter inside p
  have g_in : g ∈ K.primalNormalCell (K.projectedVertex v) ∩
      K.primalNormalCell (K.projectedVertex w) := by
    rw [← section_eq]
    exact ⟨(K.compact_normalPolygon v).isClosed.closure_eq ▸ frontier_subset_closure on_frontier,
      tight⟩
  rcases link with ⟨first, last⟩ | ⟨first, last⟩
  · change w = C.seamVertex s true at last
    rw [first, last, K.primalNormalCell_inter_endpoints_eq_segment s (Or.inl (first ▸ inside))]
      at g_in
    exact g_in
  · change w = C.seamVertex s false at last
    rw [first, last, Set.inter_comm,
      K.primalNormalCell_inter_endpoints_eq_segment s (Or.inr (first ▸ inside))] at g_in
    exact g_in

end Unfoldings.ConvexRoof
