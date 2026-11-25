module

public import Unfoldings.FewestNets.ThreeExitSegments
public import Unfoldings.Roof.SeamEmbedding
public import Unfoldings.Geometry.StraightGraphLinks
public import Unfoldings.Geometry.ParentSegments

/-! Realize the complete three-exit forest as an embedded straight cut graph. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : FewestNets.ThreeExitStemWindows}
  (R : K.ThreeExitComponentRouting seed B compact nonempty H)

local notation "U" => K.selectionComponent slopes seed
local notation "S" => K.restrictedCarrier U
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ S}
local notation "BVertices" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ frontier S}
local notation "A" => R.stems.choice.parents
local notation "G" => K.componentClippedExtension
  (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty
local notation "p" => (fun v : V => K.projectedVertex (Subtype.val v))

/-- Each original vertex starts either its directed original seam or its exterior ray. -/
def openPiece (v : V) : Set Plane := by
  classical
  exact if h : v ∈ (A).roots then R.exits.openRay (R.exitRoot ⟨v, h⟩)
    else openSegment ℝ (p v) (p ((A).parent v))

theorem openPiece_root (r : {v // v ∈ (A).roots}) :
    R.openPiece r.val = R.exits.openRay (R.exitRoot r) := by
  classical
  simp [openPiece, r.property]

theorem openPiece_stem {v : V} (h : v ∉ (A).roots) :
    R.openPiece v = openSegment ℝ (p v) (p ((A).parent v)) := by
  classical
  simp [openPiece, h]

theorem stem_edge_injective : Function.Injective R.stems.toThreeExitComponentChoices.edge := by
  intro v w equal
  have last := R.stems.toThreeExitComponentChoices.edge_link w
  rw [← equal] at last
  rcases (R.stems.toThreeExitComponentChoices.edge_link v).eq_and_eq_or_eq_and_eq last with
    same | reversed
  · exact Subtype.ext (Subtype.ext same.1)
  · have first := (A).ascending v.val v.property
    have second := (A).ascending w.val w.property
    have swap₀ : v.val = (A).parent w.val := Subtype.ext reversed.1
    have swap₁ : (A).parent v.val = w.val := Subtype.ext reversed.2
    rw [swap₁] at first
    rw [← swap₀] at second
    exact (lt_asymm first second).elim

theorem exitRoot_injective : Function.Injective R.exitRoot := by
  intro i j equal
  exact Subtype.ext (Subtype.ext (congrArg (fun r : BVertices => r.val) equal))

theorem exit_rays_disjoint :
    Pairwise (fun r s => Disjoint (R.exits.openRay r) (R.exits.openRay s)) :=
  R.exits.pairwise_disjoint_openRays_of_avoids
    (fun r => R.point_eq r ▸ (K.compact_restrictedCarrier U).isClosed.frontier_subset r.property)
    R.outside

theorem exit_openRay_disjoint_component (r : {v // v ∈ (A).roots}) :
    Disjoint (R.exits.openRay (R.exitRoot r)) S := by
  apply Set.disjoint_left.mpr
  rintro x ⟨t, ht, rfl⟩ hx
  exact R.outside _ t ht hx

theorem openPiece_avoids_original_vertices (v w : V) : p w ∉ R.openPiece v := by
  by_cases hv : v ∈ (A).roots
  · rw [R.openPiece_root ⟨v, hv⟩]
    exact fun h => Set.disjoint_left.mp (R.exit_openRay_disjoint_component ⟨v, hv⟩) h w.property
  · rw [R.openPiece_stem hv]
    exact K.seamEmbedding_straight.openSegment_avoids_vertices
      (R.stems.toThreeExitComponentChoices.edge_link ⟨v, hv⟩)

theorem openPieces_pairwise_disjoint : Pairwise (fun v w => Disjoint (R.openPiece v) (R.openPiece w)) := by
  intro v w distinct
  have stem {x : V} (hx : x ∉ (A).roots) : R.openPiece x ⊆ S := by
    rw [R.openPiece_stem hx]
    exact (openSegment_subset_segment ℝ _ _).trans
      (by rw [← R.cutLast_interior_stem 0 hx]; exact R.stem_segment_subset 0 hx)
  by_cases hv : v ∈ (A).roots
  · rw [R.openPiece_root ⟨v, hv⟩]
    by_cases hw : w ∈ (A).roots
    · rw [R.openPiece_root ⟨w, hw⟩]
      exact R.exit_rays_disjoint (fun equal => distinct
        (congrArg Subtype.val (R.exitRoot_injective equal)))
    · exact (R.exit_openRay_disjoint_component ⟨v, hv⟩).mono Set.Subset.rfl (stem hw)
  · by_cases hw : w ∈ (A).roots
    · rw [R.openPiece_root ⟨w, hw⟩]
      exact ((R.exit_openRay_disjoint_component ⟨w, hw⟩).mono Set.Subset.rfl (stem hv)).symm
    · rw [R.openPiece_stem hv, R.openPiece_stem hw]
      apply K.seamEmbedding_straight.openSegments_disjoint _
        (R.stems.toThreeExitComponentChoices.edge_link ⟨v, hv⟩)
        (R.stems.toThreeExitComponentChoices.edge_link ⟨w, hw⟩)
      exact fun equal => distinct (congrArg Subtype.val (R.stem_edge_injective equal))

variable (level : ℝ)

theorem truncatedPoint_injective
    (higher : ∀ v : V, (G).height (p v) < level) :
    Function.Injective (R.truncatedPoint level) := by
  have at_level (r : {v // v ∈ (A).roots}) :
      (G).height (R.truncatedPoint level (.inr r)) = level :=
    R.exits.pointAtLevel_height level _ (R.exit_origin_below level higher r)
  have in_ray (r : {v // v ∈ (A).roots}) :
      R.truncatedPoint level (.inr r) ∈ R.exits.openRay (R.exitRoot r) :=
    R.exits.pointAtLevel_mem_openRay level _ (R.exit_origin_below level higher r)
  intro x y same
  rcases x with v | r <;> rcases y with w | s
  · exact congrArg Sum.inl (Subtype.ext (K.projectedVertex_injective same))
  · exact ((higher v).ne ((congrArg (G).height same).trans (at_level s))).elim
  · exact ((higher w).ne ((congrArg (G).height same.symm).trans (at_level r))).elim
  · by_cases equal : r = s
    · exact congrArg Sum.inr equal
    · have distinct := R.exitRoot_injective.ne equal
      exact (Set.disjoint_left.mp (R.exit_rays_disjoint distinct) (in_ray r)
        (same.symm ▸ in_ray s)).elim

theorem truncatedSegment_subset_openPiece
    (higher : ∀ v : V, (G).height (p v) < level) (v : V) :
    openSegment ℝ (p v) (R.cutLast level v) ⊆ R.openPiece v := by
  by_cases hv : v ∈ (A).roots
  · let r : {v // v ∈ (A).roots} := ⟨v, hv⟩
    change openSegment ℝ (p r.val) (R.cutLast level r.val) ⊆ R.openPiece r.val
    have origin : R.exits.point (R.exitRoot r) = p r.val := R.point_eq _
    rw [R.cutLast_exit level r, R.openPiece_root r, ← origin]
    exact R.exits.openSegment_pointAtLevel_subset_openRay level _ (R.exit_origin_below level higher r)
  · rw [R.cutLast_interior_stem level hv, R.openPiece_stem hv]

theorem truncatedSegment_height_lt
    (higher : ∀ v : V, (G).height (p v) < level) (v : V) {x : Plane}
    (inside : x ∈ openSegment ℝ (p v) (R.cutLast level v)) :
    (G).height x < level :=
  (G).openSegment_height_lt (higher v) (R.cutLast_height_le level higher v) inside

/-- All bounded cuts are straight edges of the same rooted forest. -/
def truncatedEmbedding (higher : ∀ v : V, (G).height (p v) < level) :
    FiniteEmbeddedGraph (A).LeafVertex {v // v ∉ R.truncatedParents.roots} Plane :=
  R.truncatedParents.segmentEmbedding (R.truncatedPoint level)
    (R.truncatedPoint_injective level higher)
    (by
      intro v hv w
      cases v with
      | inr r => exact (hv ⟨r, rfl⟩).elim
      | inl v =>
        intro member
        cases w with
        | inl w =>
          exact R.openPiece_avoids_original_vertices v w
            (R.truncatedSegment_subset_openPiece level higher v member)
        | inr r =>
          have height := R.truncatedSegment_height_lt level higher v member
          have equal := R.exits.pointAtLevel_height level _ (R.exit_origin_below level higher r)
          change (G).height (R.exits.pointAtLevel level (R.exitRoot r)) < level at height
          exact (lt_irrefl _ (equal ▸ height)))
    (by
      rintro ⟨v, hv⟩ ⟨w, hw⟩ distinct
      cases v with
      | inr r => exact (hv ⟨r, rfl⟩).elim
      | inl v =>
        cases w with
        | inr r => exact (hw ⟨r, rfl⟩).elim
        | inl w =>
          exact (R.openPieces_pairwise_disjoint
            (fun equal => distinct (Subtype.ext (congrArg Sum.inl equal)))).mono
              (R.truncatedSegment_subset_openPiece level higher v)
              (R.truncatedSegment_subset_openPiece level higher w))

theorem truncatedEmbedding_straight
    (higher : ∀ v : V, (G).height (p v) < level) :
    (R.truncatedEmbedding level higher).IsStraight := fun _ _ => rfl

theorem truncatedEmbedding_rootedForest
    (higher : ∀ v : V, (G).height (p v) < level) :
    (R.truncatedEmbedding level higher).graph.IsRootedForest R.truncatedParents.roots := by
  unfold truncatedEmbedding
  apply AscendingParents.segmentEmbedding_rootedForest

theorem truncatedEmbedding_carrier_eq
    (higher : ∀ v : V, (G).height (p v) < level) :
    (R.truncatedEmbedding level higher).carrier =
      ⋃ v : V, segment ℝ (p v) (R.cutLast level v) := by
  let F := R.truncatedEmbedding level higher
  have member (v : V) : segment ℝ (p v) (R.cutLast level v) ⊆ F.carrier := by
    intro x on_segment
    obtain ⟨t, ht, equal⟩ := (segment_eq_image_lineMap ℝ _ _).subset on_segment
    let edge : {v // v ∉ R.truncatedParents.roots} :=
      ⟨.inl v, (A).withLeaves_inl_nonroot R.leafRank R.height_lt_leafRank v⟩
    have loc : F.edge edge ⟨t, ht⟩ = x := equal
    exact loc ▸ F.mem_carrier_edge edge ⟨t, ht⟩
  apply Set.Subset.antisymm _ (Set.iUnion_subset member)
  intro x on_graph
  obtain ⟨v | e, loc⟩ := Set.mem_iUnion.mp on_graph
  · change x = F.vertex v at loc
    subst x
    rcases v with v | r
    · exact Set.mem_iUnion.mpr ⟨v, left_mem_segment ℝ _ _⟩
    · refine Set.mem_iUnion.mpr ⟨r.val, ?_⟩
      rw [R.cutLast_exit level r]
      exact right_mem_segment ℝ _ _
  · obtain ⟨t, rfl⟩ : ∃ t, F.edge e t = x := loc
    obtain ⟨v | r, nonroot⟩ := e
    · exact Set.mem_iUnion.mpr ⟨v, lineMap_mem_segment ℝ _ _ t.property⟩
    · exact (nonroot ⟨r, rfl⟩).elim

/-- Every point of the cut carrier in the section's interior has a remaining
forward piece. An endpoint of one stem uses its next parent or exit segment. -/
theorem exists_truncated_forward_piece
    (higher : ∀ v : V, (G).height (p v) < level) {x : Plane}
    (member : x ∈ (R.truncatedEmbedding level higher).carrier)
    (internal : x ∈ interior {z | (G).height z ≤ level}) :
    ∃ v : V, x ∈ segment ℝ (p v) (R.cutLast level v) ∧ x ≠ R.cutLast level v := by
  rw [R.truncatedEmbedding_carrier_eq level higher] at member
  obtain ⟨v, on_segment⟩ := Set.mem_iUnion.mp member
  by_cases last : x = R.cutLast level v
  · unfold cutLast at last
    cases next : R.truncatedParents.parent (.inl v) with
    | inl w =>
      rw [next] at last
      change x = p w at last
      exact ⟨w, last.symm ▸ (left_mem_segment ℝ (p w) (R.cutLast level w)),
        last.symm ▸ R.cutLast_ne_cutFirst level higher w⟩
    | inr r =>
      rw [next] at last
      change x = R.exits.pointAtLevel level (R.exitRoot r) at last
      have rim := R.exits.pointAtLevel_mem_frontier level _ (R.exit_origin_below level higher r)
      exact (rim.2 (last ▸ internal)).elim
  · exact ⟨v, on_segment, last⟩

end Unfoldings.ConvexRoof.ThreeExitComponentRouting
