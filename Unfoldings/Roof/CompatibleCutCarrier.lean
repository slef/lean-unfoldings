module

public import Unfoldings.Roof.CompatiblePotentialRouting
public import Unfoldings.Roof.ClippedPhysicalCurvature

/-! Actual cuts retain selected original edges and cover all extension curvature vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem seam_segment_subset_selectedCarrier {slopes : Set Plane} {v w : C.Vertex Set.univ}
    (inside : K.projectedVertex v ∈ interior (K.selectedCarrier slopes)) {s : C.Seam}
    (link : C.seamGraph.IsLink s v w) :
    segment ℝ (K.projectedVertex v) (K.projectedVertex w) ⊆ K.selectedCarrier slopes := by
  let f := (C.left s).face
  have endpoint (b : Bool) :
      K.projectedVertex (C.seamVertex s b) ∈ (K.projectedTriangle f).carrier := by
    cases b
    · exact (K.projectedTriangle f).vertex_mem (C.left s).edge
    · exact (K.projectedTriangle f).vertex_mem (Triangle.next (C.left s).edge)
  have first : K.projectedVertex v ∈ (K.projectedTriangle f).carrier := by
    rcases link with ⟨equal, _⟩ | ⟨equal, _⟩
    · exact equal.symm ▸ endpoint false
    · exact equal.symm ▸ endpoint true
  have last : K.projectedVertex w ∈ (K.projectedTriangle f).carrier := by
    rcases link with ⟨_, equal⟩ | ⟨_, equal⟩
    · exact equal.symm ▸ endpoint true
    · exact equal.symm ▸ endpoint false
  have selected := K.selected_of_mem_interior_selectedCarrier inside f first
  intro p hp
  exact K.mem_selectedCarrier.mpr ⟨f, selected,
    (K.projectedTriangle f).convex_carrier.segment_subset first last hp⟩

namespace CompatiblePotentialRouting

variable {K} {U : Set Face} {G : SlopeEnvelope}
  {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

def terminalIndex (v : {v // v ∈ R.parents.roots}) : {v // v ∈ R.original.parents.roots} :=
  ⟨v.val, v.property.choose⟩

/-- Finite parent segments together with the actual straight continuations at final roots. -/
def carrier : Set Plane :=
  (⋃ v : {v // v ∉ R.parents.roots},
    segment ℝ (K.projectedVertex v.val) (K.projectedVertex (R.parents.parent v.val))) ∪
  (⋃ v : {v // v ∈ R.parents.roots},
    {x | ∃ t : ℝ, 0 ≤ t ∧ x = R.exterior.ray (R.terminalIndex v) t})

theorem vertex_mem_carrier (v : C.Vertex Set.univ) : K.projectedVertex v ∈ R.carrier := by
  classical
  by_cases root : v ∈ R.parents.roots
  · apply Or.inr
    apply Set.mem_iUnion.mpr
    refine ⟨⟨v, root⟩, 0, le_rfl, ?_⟩
    simp only [SlopeEnvelope.ExteriorPlan.ray, zero_smul, add_zero, R.exterior_points]
    rfl
  · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨v, root⟩, left_mem_segment ℝ _ _⟩)

end CompatiblePotentialRouting

variable {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)

/-- All preserved original parent edges lie in the selected closed faces. -/
theorem compatible_original_segment_selected {v : C.Vertex Set.univ}
    (nonroot : v ∉ R.original.parents.roots) :
    segment ℝ (K.projectedVertex v) (K.projectedVertex (R.parents.parent v)) ⊆
      K.selectedCarrier slopes := by
  have inside : K.projectedVertex v ∈ interior (K.selectedCarrier slopes) := by
    by_contra outside
    exact nonroot ((Set.ext_iff.mp R.original.roots_eq v).mpr outside)
  rw [R.original_parent nonroot]
  exact K.seam_segment_subset_selectedCarrier inside (R.original.selection.link ⟨v, nonroot⟩)

/-- Every positive-time exterior point avoids all closed selected original faces. -/
theorem compatible_exterior_ray_avoids_selected
    (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
    (r : {v // v ∈ R.original.parents.roots}) {t : ℝ} (positive : 0 < t)
    (f : Face) (selected : K.normalSlope f ∈ slopes) :
    R.exterior.ray r t ∉ (K.projectedTriangle f).carrier := by
  have inside : K.normalSlope f ∈ interior slopes := by
    by_contra outside
    exact no_boundary f ⟨subset_closure selected, outside⟩
  have nonzero : R.exterior.direction (R.exterior.slope r) ≠ 0 := by
    intro zero
    have unit := R.exterior.unit r
    rw [zero, norm_zero] at unit
    norm_num at unit
  exact K.clippedExtension_ray_avoids_selected_faces compact nonempty (R.exterior.active r)
    rfl (R.exterior.support r) nonzero positive f inside

variable (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel) {Z : ℝ}
  (T : SpatialEnvelope.Triangulation M.plane Z)
  (conforming : TriangleFamily.Conforming T.projectedTriangle)
  (inside : (interior (SpatialEnvelope.clip M.plane Z)).Nonempty)

local instance : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- The constructed full cut carrier covers every actual positive-curvature extension vertex. -/
theorem compatible_carrier_covers_positive_curvature (convex : Convex ℝ slopes)
    (v : T.pairedComplex.Vertex Set.univ)
    (curved : 0 < T.pairedComplex.interiorAngularDefect Set.univ v) :
    (T.roof conforming inside).projectedVertex v ∈ R.carrier := by
  obtain ⟨⟨f, i⟩, equal, _height⟩ := K.clippedPhysical_positive_curvature_original_corner
    compact nonempty M T conforming inside convex v curved
  have corner := R.vertex_mem_carrier (C.vertexOfCorner Set.univ (f, i))
  rw [K.projectedVertex_ofCorner] at corner
  exact equal ▸ corner

end Unfoldings.ConvexRoof
