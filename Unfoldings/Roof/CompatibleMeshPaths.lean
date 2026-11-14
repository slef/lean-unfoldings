module

public import Unfoldings.Roof.CompatibleMeshSubedges

/-! Fine mesh parents follow the original compatible routing and retain its whole-path bounds. -/

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

local instance compatibleMeshPathIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

theorem compatibleMesh_parent_follows (v : (T).pairedComplex.Vertex Set.univ)
    (nonroot : v ∉ (Fcut).parents.roots) :
    R.FollowsStep ((Q).projectedVertex v) ((Q).projectedVertex ((Fcut).parents.parent v)) := by
  let e : {v // v ∉ (Fcut).parents.roots} := ⟨v, nonroot⟩
  let s := (Fcut).selection.edge e
  have selected := (Fcut).selected_subset e
  rw [(T).toTriangulation.roof_projectedTriangle conforming inside] at selected
  obtain ⟨i, contained⟩ := K.compatibleMesh_subedge compact nonempty R no_boundary level higher
    M positive inner_disk ((T).pairedComplex.left s) selected
  have first : (Q).projectedVertex v ∈
      ((Q).projectedTriangle ((T).pairedComplex.left s).face).edge
        ((T).pairedComplex.left s).edge := by
    rcases (Fcut).selection.link e with ⟨first, _last⟩ | ⟨first, _last⟩
    · change v = (T).pairedComplex.seamVertex s false at first
      rw [first]
      exact left_mem_segment ℝ _ _
    · change v = (T).pairedComplex.seamVertex s true at first
      rw [first]
      exact right_mem_segment ℝ _ _
  have last : (Q).projectedVertex ((Fcut).parents.parent v) ∈
      ((Q).projectedTriangle ((T).pairedComplex.left s).face).edge
        ((T).pairedComplex.left s).edge := by
    rcases (Fcut).selection.link e with ⟨_first, last⟩ | ⟨_first, last⟩
    · change (Fcut).parents.parent v = (T).pairedComplex.seamVertex s true at last
      rw [last]
      exact right_mem_segment ℝ _ _
    · change (Fcut).parents.parent v = (T).pairedComplex.seamVertex s false at last
      rw [last]
      exact left_mem_segment ℝ _ _
  rw [(T).toTriangulation.roof_projectedTriangle conforming inside] at first last
  have increasing := (Fcut).parents.ascending v nonroot
  rw [(Fcut).height_eq] at increasing
  exact K.followsStep_of_truncated_segment compact nonempty R no_boundary level higher
    positive inner_disk beta acute (contained first) (contained last) increasing

/-- Any initial finite portion of an actual fine parent orbit. -/
def compatibleMeshHistory (start : (T).pairedComplex.Vertex Set.univ) (n : ℕ) :
    PolygonalChain Plane n :=
  ⟨fun i => (Q).projectedVertex ((Fcut).parents.parent^[i.val] start)⟩

theorem compatibleMeshHistory_follows (start : (T).pairedComplex.Vertex Set.univ) (n : ℕ)
    (before : n ≤ (Fcut).parents.distanceToRoot start) :
    R.Follows (K.compatibleMeshHistory compact nonempty R no_boundary level higher M
      positive inner_disk beta acute start n) := by
  intro i
  change R.FollowsStep ((Q).projectedVertex ((Fcut).parents.parent^[i.val] start))
    ((Q).projectedVertex ((Fcut).parents.parent^[i.val + 1] start))
  rw [Function.iterate_succ_apply']
  exact K.compatibleMesh_parent_follows compact nonempty R no_boundary level higher M
    positive inner_disk beta acute _
    ((Fcut).parents.iterate_lt_distanceToRoot_not_mem start (lt_of_lt_of_le i.isLt before))

theorem compatibleMeshHistory_length_bound {b : ℝ} (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)
    (start : (T).pairedComplex.Vertex Set.univ) (n : ℕ)
    (before : n ≤ (Fcut).parents.distanceToRoot start) :
    (K.compatibleMeshHistory compact nonempty R no_boundary level higher M
      positive inner_disk beta acute start n).projectedLength ≤ (b / (a * Real.cos β)) *
        ‖(Q).projectedVertex ((Fcut).parents.parent^[n] start) - (Q).projectedVertex start‖ :=
  R.follows_length_bound positive beta acute inner_disk upper _
    (K.compatibleMeshHistory_follows compact nonempty R no_boundary level higher M
      positive inner_disk beta acute start n before)

end Unfoldings.ConvexRoof
