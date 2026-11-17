module

public import Unfoldings.Roof.CompatibleProcessedWindowCarrier
public import Unfoldings.Geometry.PrescribedCutMetric

/-! Canonical finite segment constraints for larger original intermediate-cut windows. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

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

local instance processedWindowSegmentsIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S

open Classical in
/-- All actual old processed edge endpoints and original terminal endpoints in the new window.
The finite set lies in a fixed Euclidean type, independently of the original mesh universe. -/
def compatibleMeshProcessedWindowPairs (S : (Fcut).parents.ParentFrontier) (later : ℝ) :
    Finset (Plane × Plane) :=
  (Finset.univ.image fun s : (T).pairedComplex.CutSeam RetainAt[S] =>
    (((Q).projectedTriangle ((T).pairedComplex.left s.val).face).vertex
      ((T).pairedComplex.left s.val).edge,
    ((Q).projectedTriangle ((T).pairedComplex.left s.val).face).vertex
      (Triangle.next ((T).pairedComplex.left s.val).edge))) ∪
  (Finset.univ.image fun r : {v // v ∈ R.parents.roots} =>
    (R.terminalPoint level r, R.terminalPoint later r))

local notation "PairsAt[" S "," L "]" => K.compatibleMeshProcessedWindowPairs compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S L

open Classical in
/-- A strictly larger window gives genuine original segments for all canonical constraints. -/
theorem compatibleMeshProcessedWindowPairs_ne (S : (Fcut).parents.ParentFrontier)
    {later : ℝ} (ordered : level < later) (pair : {p // p ∈ PairsAt[S,later]}) :
    pair.val.1 ≠ pair.val.2 := by
  rcases pair with ⟨pair, member⟩
  rcases Finset.mem_union.mp member with old | terminal
  · obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp old
    exact ((Q).projectedTriangle ((T).pairedComplex.left s.val).face).edge_endpoints_ne _
  · obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp terminal
    intro same
    have at_old := R.terminalPoint_level level higher r
    have at_new := R.terminalPoint_level later (fun v => (higher v).trans ordered) r
    have heights := congrArg (K.clippedExtension slopes compact nonempty).height same
    rw [at_old, at_new] at heights
    exact ordered.ne heights

open Classical in
/-- The canonical finite constraints describe exactly the same original comparison cut. -/
theorem compatibleMeshProcessedWindowCarrier_eq_pairs (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) :
    K.compatibleMeshProcessedWindowCarrier compact nonempty R no_boundary level higher M positive
        inner_disk beta acute S later =
      ⋃ pair : {p // p ∈ PairsAt[S,later]}, segment ℝ pair.val.1 pair.val.2 := by
  rw [K.compatibleMeshProcessedWindowCarrier_eq_union_edges]
  ext x
  constructor
  · intro member
    rcases member with old | terminal
    · obtain ⟨s, on_edge⟩ := Set.mem_iUnion.mp old
      refine Set.mem_iUnion.mpr ⟨⟨_, Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩)⟩, on_edge⟩
    · obtain ⟨r, on_tail⟩ := Set.mem_iUnion.mp terminal
      refine Set.mem_iUnion.mpr ⟨⟨_, Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)⟩, on_tail⟩
  · intro member
    obtain ⟨⟨pair, member⟩, on_segment⟩ := Set.mem_iUnion.mp member
    rcases Finset.mem_union.mp member with old | terminal
    · obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp old
      exact Or.inl (Set.mem_iUnion.mpr ⟨s, on_segment⟩)
    · obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp terminal
      exact Or.inr (Set.mem_iUnion.mpr ⟨r, on_segment⟩)

end Unfoldings.ConvexRoof
