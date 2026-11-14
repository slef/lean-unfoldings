module

public import Unfoldings.Roof.CompatibleMeshOrientation

/-! The selected fine cutting forest is exactly the complete prescribed geometric cut network. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)
  (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
  (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ slopes)
  (beta : 0 ≤ β) (acute : β < Real.pi / 2)

local notation "T" => K.compatibleCutMesh compact nonempty R no_boundary level higher M
  positive inner_disk
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance compatibleMeshRetentionIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "B" => SlopeEnvelope.boundaryEnvelope
  (K.clippedExtension slopes compact nonempty) boundary
local notation "Gcut" => K.truncatedCutEmbedding compact nonempty R no_boundary level higher


include beta acute in
theorem compatibleMesh_cut_height_ne (s : (T).pairedComplex.Seam)
    (selected : ((T).projectedTriangle ((T).pairedComplex.left s).face).edge
      ((T).pairedComplex.left s).edge ⊆ R.truncatedCarrier level higher) :
    (B).height ((Q).projectedVertex ((T).pairedComplex.seamVertex s false)) ≠
      (B).height ((Q).projectedVertex ((T).pairedComplex.seamVertex s true)) := by
  obtain ⟨i, contained⟩ := K.compatibleMesh_subedge compact nonempty R no_boundary level higher
    M positive inner_disk ((T).pairedComplex.left s) selected
  have first : (Q).projectedVertex ((T).pairedComplex.seamVertex s false) ∈
      ((T).projectedTriangle ((T).pairedComplex.left s).face).edge
        ((T).pairedComplex.left s).edge := by
    rw [← (T).toTriangulation.roof_projectedTriangle conforming inside]
    exact left_mem_segment ℝ _ _
  have last : (Q).projectedVertex ((T).pairedComplex.seamVertex s true) ∈
      ((T).projectedTriangle ((T).pairedComplex.left s).face).edge
        ((T).pairedComplex.left s).edge := by
    rw [← (T).toTriangulation.roof_projectedTriangle conforming inside]
    exact right_mem_segment ℝ _ _
  intro equal
  have same := K.cut_segment_height_injective compact nonempty R no_boundary level higher
    positive inner_disk beta acute i (contained first) (contained last) equal
  exact (Q).seamEmbedding.vertex_injective.ne ((Q).seamEmbedding_straight.endpoints_ne s) same

theorem compatibleMesh_ascending_cut_selected {s : (T).pairedComplex.Seam}
    {v w : (T).pairedComplex.Vertex Set.univ} (link : (T).pairedComplex.seamGraph.IsLink s v w)
    (selected : ((T).projectedTriangle ((T).pairedComplex.left s).face).edge
      ((T).pairedComplex.left s).edge ⊆ R.truncatedCarrier level higher)
    (increasing : (B).height ((Q).projectedVertex v) < (B).height ((Q).projectedVertex w)) :
    s ∈ Set.range (Fcut).selection.edge := by
  obtain ⟨P⟩ := K.compatibleMesh_oriented_seam compact nonempty R no_boundary level higher
    positive inner_disk beta acute M link selected increasing
  have strict := K.oriented_truncated_start_strict compact nonempty R no_boundary level higher P
  have interior_point : (Q).projectedVertex v ∈ interior (Q).footprint := by
    rw [(T).toTriangulation.roof_footprint conforming inside, M.clip_eq_sublevel, neg_neg]
    exact (K.clippedExtension slopes compact nonempty).mem_interior_sublevel strict
  have nonroot : v ∉ (Fcut).parents.roots := by
    intro root
    rcases (Set.ext_iff.mp (Fcut).roots_eq v).mp root with boundary | outside
    · exact ((Q).projectedVertex_mem_interior_iff v).mp interior_point boundary
    · apply outside
      have equal := (Q).projected_link_segment link
      rw [(T).toTriangulation.roof_projectedTriangle conforming inside] at equal
      exact selected (equal ▸ left_mem_segment ℝ _ _)
  let e : {v // v ∉ (Fcut).parents.roots} := ⟨v, nonroot⟩
  have parent_selected := (Fcut).selected_subset e
  rw [(T).toTriangulation.roof_projectedTriangle conforming inside] at parent_selected
  have parent_increasing := (Fcut).parents.ascending v nonroot
  rw [(Fcut).height_eq] at parent_increasing
  obtain ⟨parent_P⟩ := K.compatibleMesh_oriented_seam compact nonempty R no_boundary level higher
    positive inner_disk beta acute M ((Fcut).selection.link e) parent_selected parent_increasing
  have same := FiniteEmbeddedGraph.fine_forward_edge_unique Gcut
    (K.truncatedCutEmbedding_straight compact nonempty R no_boundary level higher)
    Subtype.val_injective (Q).seamEmbedding_straight link ((Fcut).selection.link e) P parent_P
  exact ⟨e, same.symm⟩

/-- The cut seams are exactly all whole mesh edges in the prescribed compatible cut carrier. -/
theorem compatibleMesh_retain_eq_prescribed :
    (Fcut).retain = (T).toTriangulation.retainOutside (R.truncatedCarrier level higher) := by
  ext s
  constructor
  · intro kept
    by_contra cut
    have selected : ((T).projectedTriangle ((T).pairedComplex.left s).face).edge
        ((T).pairedComplex.left s).edge ⊆ R.truncatedCarrier level higher := not_not.mp cut
    have different := K.compatibleMesh_cut_height_ne compact nonempty R no_boundary level higher
      M positive inner_disk beta acute s selected
    rcases lt_or_gt_of_ne different with increasing | increasing
    · exact kept (K.compatibleMesh_ascending_cut_selected compact nonempty R no_boundary
        level higher M positive inner_disk beta acute (Or.inl ⟨rfl, rfl⟩) selected increasing)
    · exact kept (K.compatibleMesh_ascending_cut_selected compact nonempty R no_boundary
        level higher M positive inner_disk beta acute (Or.inr ⟨rfl, rfl⟩) selected increasing)
  · intro kept selected
    obtain ⟨e, rfl⟩ := selected
    apply kept
    have contained := (Fcut).selected_subset e
    rw [(T).toTriangulation.roof_projectedTriangle conforming inside] at contained
    exact contained

end Unfoldings.ConvexRoof
