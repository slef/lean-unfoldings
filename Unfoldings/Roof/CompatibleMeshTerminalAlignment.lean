module

public import Unfoldings.Roof.CompatibleCutMesh
public import Unfoldings.Geometry.PrescribedSubedge
public import Unfoldings.Geometry.SpatialEnvelopeDirectedBanks
public import Unfoldings.Complex.DirectedBoundaryPathReversal

/-! Nonvertex contact identifies an entire original fine edge with one named terminal segment. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)
  (level : ℝ) (higher : ∀ v, G.height (K.projectedVertex v) < level)

include higher in
/-- Every point of the original terminal segment has a parameter in the actual terminal interval. -/
theorem exists_terminal_parameter_of_mem_segment (r : {v // v ∈ R.parents.roots})
    {p : Plane} (member : p ∈ segment ℝ (K.projectedVertex r.val) (R.terminalPoint level r)) :
    ∃ t : Set.Icc (0 : ℝ) (R.terminalTime level r),
      p = R.exterior.ray (R.terminalIndex r) t.val := by
  obtain ⟨u, bounds, equal⟩ := (segment_eq_image_lineMap ℝ _ _).subset member
  refine ⟨⟨u * R.terminalTime level r,
    mul_nonneg bounds.1 (R.terminalTime_pos level higher r).le,
    mul_le_of_le_one_left (R.terminalTime_pos level higher r).le bounds.2⟩, ?_⟩
  exact equal.symm.trans (R.terminal_lineMap_eq_ray level r u)

include higher in
/-- The original whole ray up to its actual terminal time is precisely on the terminal segment. -/
theorem terminal_ray_mem_segment (r : {v // v ∈ R.parents.roots})
    (t : Set.Icc (0 : ℝ) (R.terminalTime level r)) :
    R.exterior.ray (R.terminalIndex r) t.val ∈
      segment ℝ (K.projectedVertex r.val) (R.terminalPoint level r) := by
  have positive := R.terminalTime_pos level higher r
  have member := lineMap_mem_segment ℝ (K.projectedVertex r.val) (R.terminalPoint level r)
    (show t.val / R.terminalTime level r ∈ Set.Icc (0 : ℝ) 1 from
      ⟨div_nonneg t.property.1 positive.le, (div_le_one positive).mpr t.property.2⟩)
  rwa [R.terminal_lineMap_eq_ray, div_mul_cancel₀ _ positive.ne'] at member

end Unfoldings.ConvexRoof.CompatiblePotentialRouting

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

local instance terminalAlignmentIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

/-- Retain the identity of the prescribed segment, rather than merely the union of all cuts. -/
theorem compatibleCutMesh_segment_aligned
    (i : Fin (Fintype.card (C.Vertex Set.univ))) (f : (T).Index) (e : Fin 3)
    (x : ((T).projectedTriangle f).Edge e) (regular : ¬ ((T).projectedTriangle f).IsVertex x.val)
    (member : x.val ∈ segment ℝ (R.cutFirst level i) (R.cutLast level higher i)) :
    ((T).projectedTriangle f).edge e ⊆
      segment ℝ (R.cutFirst level i) (R.cutLast level higher i) := by
  let U := triangleWithEdge (R.cutFirst level i) (R.cutLast level higher i)
    (K.cut_endpoints_ne compact nonempty R no_boundary level higher i)
  exact U.edge_subset_of_signed_coords ((T).projectedTriangle f)
    (fun k => (T).signs f (.inr (i, k)))
    (fun k p hp => (T).constrained f p hp (.inr (i, k))) 0 e x regular member

/-- A contact with a terminal segment away from fine vertices forces the entire original edge
inside that same terminal segment, including both original fine endpoints. -/
theorem compatibleCutMesh_terminal_segment_aligned
    (r : {v // v ∈ R.parents.roots}) (f : (T).Index) (e : Fin 3)
    (x : ((T).projectedTriangle f).Edge e) (regular : ¬ ((T).projectedTriangle f).IsVertex x.val)
    (member : x.val ∈ segment ℝ (K.projectedVertex r.val) (R.terminalPoint level r)) :
    ((T).projectedTriangle f).edge e ⊆
      segment ℝ (K.projectedVertex r.val) (R.terminalPoint level r) := by
  let i := (Fintype.equivFin (C.Vertex Set.univ)) r.val
  have first : R.cutFirst level i = K.projectedVertex r.val := by
    simp only [CompatiblePotentialRouting.cutFirst, i, Equiv.symm_apply_apply,
      CompatiblePotentialRouting.truncatedPoint]
  have last : R.cutLast level higher i = R.terminalPoint level r := by
    change R.truncatedPoint level ((R.truncatedParents level higher).parent
      (.inl ((Fintype.equivFin (C.Vertex Set.univ)).symm i))) = _
    rw [(Fintype.equivFin (C.Vertex Set.univ)).symm_apply_apply r.val]
    rw [show (R.truncatedParents level higher).parent (.inl r.val) = .inr r from
      R.parents.withLeaves_parent_root level _ r]
    rfl
  have contact : x.val ∈ segment ℝ (R.cutFirst level i) (R.cutLast level higher i) := by
    rw [first, last]
    exact member
  have aligned := K.compatibleCutMesh_segment_aligned compact nonempty R no_boundary level higher
    M positive inner_disk i f e x regular contact
  rwa [first, last] at aligned

/-- A nonvertex point of an original directed bank identifies its entire projected trace
with a single original terminal segment. -/
theorem compatibleMesh_directedBank_terminal_segment
    {retain : Set (T).pairedComplex.Seam} (r : {v // v ∈ R.parents.roots})
    (p : (T).pairedComplex.BoundaryEnd retain) (t : unitInterval)
    (regular : ∀ v : (T).pairedComplex.Vertex retain,
      (T).pairedComplex.directedBoundaryPath p t ≠ (T).pairedComplex.vertexPoint retain v)
    (member : Cap.horizontal ((T).pairedFolding.toSpace retain
      ((T).pairedComplex.directedBoundaryPath p t)) ∈
        segment ℝ (K.projectedVertex r.val) (R.terminalPoint level r)) :
    ∀ u : unitInterval, Cap.horizontal ((T).pairedFolding.toSpace retain
      ((T).pairedComplex.directedBoundaryPath p u)) ∈
        segment ℝ (K.projectedVertex r.val) (R.terminalPoint level r) := by
  let bank := ((T).pairedComplex.boundaryEndEquiv retain p).1
  have aligned := K.compatibleCutMesh_terminal_segment_aligned compact nonempty R no_boundary level
    higher M positive inner_disk r bank.val.face bank.val.edge
    ⟨_, (T).toTriangulation.horizontal_directedBoundaryPath_mem_edge p t⟩
    ((T).toTriangulation.horizontal_directedBoundaryPath_nonvertex p t regular) member
  exact fun u => aligned ((T).toTriangulation.horizontal_directedBoundaryPath_mem_edge p u)

/-- Orient an original fine bank forward along its named terminal segment. Endpoint bounds,
orientation and retention of the original contact copy follow from one nonvertex contact. -/
theorem exists_compatibleMesh_forward_terminal_bank
    {retain : Set (T).pairedComplex.Seam} (r : {v // v ∈ R.parents.roots})
    (p : (T).pairedComplex.BoundaryEnd retain) (u : unitInterval)
    (regular : ∀ v : (T).pairedComplex.Vertex retain,
      (T).pairedComplex.directedBoundaryPath p u ≠ (T).pairedComplex.vertexPoint retain v)
    (member : Cap.horizontal ((T).pairedFolding.toSpace retain
      ((T).pairedComplex.directedBoundaryPath p u)) ∈
        segment ℝ (K.projectedVertex r.val) (R.terminalPoint level r)) :
    ∃ (q : (T).pairedComplex.BoundaryEnd retain)
      (s t : Set.Icc (0 : ℝ) (R.terminalTime level r)), s.val < t.val ∧
      Cap.horizontal ((T).pairedFolding.boundaryPosition q) =
        R.exterior.ray (R.terminalIndex r) s.val ∧
      Cap.horizontal ((T).pairedFolding.boundaryPosition
        ((T).pairedComplex.boundaryTurn retain q)) =
          R.exterior.ray (R.terminalIndex r) t.val ∧
      ∃ v : unitInterval, (T).pairedComplex.directedBoundaryPath q v =
        (T).pairedComplex.directedBoundaryPath p u := by
  have entire := K.compatibleMesh_directedBank_terminal_segment compact nonempty R no_boundary
    level higher M positive inner_disk r p u regular member
  have first_member : Cap.horizontal ((T).pairedFolding.boundaryPosition p) ∈
      segment ℝ (K.projectedVertex r.val) (R.terminalPoint level r) := by
    have initial := entire 0
    rw [(T).pairedFolding.horizontal_directedBoundaryPath] at initial
    change AffineMap.lineMap _ _ (0 : ℝ) ∈ _ at initial
    simpa only [AffineMap.lineMap_apply_zero] using initial
  have last_member : Cap.horizontal ((T).pairedFolding.boundaryPosition
      ((T).pairedComplex.boundaryTurn retain p)) ∈
      segment ℝ (K.projectedVertex r.val) (R.terminalPoint level r) := by
    have final := entire 1
    rw [(T).pairedFolding.horizontal_directedBoundaryPath] at final
    change AffineMap.lineMap _ _ (1 : ℝ) ∈ _ at final
    simpa only [AffineMap.lineMap_apply_one] using final
  obtain ⟨s, first⟩ := R.exists_terminal_parameter_of_mem_segment level higher r first_member
  obtain ⟨t, last⟩ := R.exists_terminal_parameter_of_mem_segment level higher r last_member
  have different : s.val ≠ t.val := by
    intro same
    exact (T).toTriangulation.horizontal_boundaryPosition_ne p
      (first.trans ((congrArg (R.exterior.ray (R.terminalIndex r)) same).trans last.symm))
  rcases lt_or_gt_of_ne different with forward | backward
  · exact ⟨p, s, t, forward, first, last, u, rfl⟩
  · refine ⟨(T).pairedComplex.boundaryTurn retain p, t, s, backward, last, ?_, ?_⟩
    · rwa [(T).pairedComplex.boundaryTurn_involutive]
    · refine ⟨⟨1 - u.val, sub_nonneg.mpr u.property.2, sub_le_self _ u.property.1⟩, ?_⟩
      rw [(T).pairedComplex.directedBoundaryPath_turn]
      apply congrArg ((T).pairedComplex.directedBoundaryPath p)
      apply Subtype.ext
      change 1 - (1 - u.val) = u.val
      ring

end Unfoldings.ConvexRoof
