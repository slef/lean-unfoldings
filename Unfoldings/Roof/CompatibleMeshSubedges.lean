module

public import Unfoldings.Roof.CompatibleMeshForest
public import Unfoldings.Geometry.PrescribedSubedge

/-! Every selected whole fine edge lies in one oriented original compatible cut segment. -/

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

local notation "T" => K.compatibleCutMesh compact nonempty R no_boundary level higher M
  positive inner_disk

local instance compatibleMeshSubedgeIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

theorem compatibleMesh_subedge (e : EdgeRef (T).Index)
    (selected : ((T).projectedTriangle e.face).edge e.edge ⊆ R.truncatedCarrier level higher) :
    ∃ i, ((T).projectedTriangle e.face).edge e.edge ⊆
      segment ℝ (R.cutFirst level i) (R.cutLast level higher i) := by
  obtain ⟨x, regular⟩ := ((T).projectedTriangle e.face).exists_edge_nonvertex e.edge
  have member := selected x.property
  rw [R.truncatedCarrier_eq_segments level higher] at member
  obtain ⟨i, on_segment⟩ := Set.mem_iUnion.mp member
  let U := triangleWithEdge (R.cutFirst level i) (R.cutLast level higher i)
    (K.cut_endpoints_ne compact nonempty R no_boundary level higher i)
  refine ⟨i, U.edge_subset_of_signed_coords ((T).projectedTriangle e.face)
    (fun k => (T).signs e.face (.inr (i, k))) ?_ 0 e.edge x regular on_segment⟩
  intro k p hp
  exact (T).constrained e.face p hp (.inr (i, k))

variable (beta : 0 ≤ β) (acute : β < Real.pi / 2)

include no_boundary positive inner_disk beta acute in
theorem followsStep_of_truncated_segment {i : Fin (Fintype.card (C.Vertex Set.univ))}
    {x y : Plane} (first : x ∈ segment ℝ (R.cutFirst level i) (R.cutLast level higher i))
    (last : y ∈ segment ℝ (R.cutFirst level i) (R.cutLast level higher i))
    (increasing :
      ((K.clippedExtension slopes compact nonempty).boundaryEnvelope boundary).height x <
      ((K.clippedExtension slopes compact nonempty).boundaryEnvelope boundary).height y) :
    R.FollowsStep x y := by
  obtain ⟨s, hs, at_first⟩ := (segment_eq_image_lineMap ℝ _ _).subset first
  obtain ⟨t, ht, at_last⟩ := (segment_eq_image_lineMap ℝ _ _).subset last
  let v := (Fintype.equivFin (C.Vertex Set.univ)).symm i
  have strict : StrictMonoOn (fun t : ℝ =>
      ((K.clippedExtension slopes compact nonempty).boundaryEnvelope boundary).height
        (AffineMap.lineMap (R.cutFirst level i) (R.cutLast level higher i) t))
      (Set.Icc 0 1) := K.truncated_segment_strict compact nonempty R no_boundary level higher
        positive beta acute inner_disk v
  have ordered : s ≤ t := by
    by_contra reversed
    have bound := strict.monotoneOn ht hs (le_of_lt (lt_of_not_ge reversed))
    rw [at_first, at_last] at bound
    exact (not_lt_of_ge bound) increasing
  rw [← at_first, ← at_last]
  exact R.truncated_segment_follows level higher v hs.1 ordered ht.2

end Unfoldings.ConvexRoof
