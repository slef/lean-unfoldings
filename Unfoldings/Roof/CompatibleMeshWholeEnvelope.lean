module

public import Unfoldings.Roof.CompatibleCutMesh
public import Unfoldings.Roof.CompatibleWholeCutModel
public import Unfoldings.Roof.SpatialEnvelopeSupportRecovery
public import Unfoldings.Roof.CompletionCombinedConstraints

/-! Choose actual compatible clips preserving the entire unbounded supporting envelope. -/

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
  (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
  (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ slopes)

variable (W : R.WholeCutModel M)

local instance wholeEnvelopeIndexFintype : Fintype W.Index := W.finiteIndex

/-- Choose the truncation after seeing all original whole support cells. All original
vertices lie strictly below it, and every whole affine support survives in the finite mesh. -/
theorem exists_compatibleMesh_support_level (lower : ℝ) :
    ∃ level : ℝ, lower < level ∧
      (∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level) ∧
      ∀ c, (interior (W.partition.footprint c) ∩
        interior (SpatialEnvelope.clip M.plane (-level))).Nonempty := by
  obtain ⟨bound, bounded⟩ := (Set.finite_range
    (fun v : C.Vertex Set.univ =>
      (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v))).bddAbove
  obtain ⟨level, large, captures⟩ :=
    SpatialEnvelope.exists_level_capturing_support_cells W.partition (max lower bound)
  refine ⟨level, (le_max_left _ _).trans_lt large, ?_, captures level le_rfl⟩
  intro v
  exact (bounded (Set.mem_range_self v)).trans_lt ((le_max_right _ _).trans_lt large)

variable (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)

local notation "T" => K.compatibleCutMesh compact nonempty R no_boundary level higher M
  positive inner_disk
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside

local instance wholeEnvelopeMeshIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (captured : ∀ c, (interior (W.partition.footprint c) ∩
  interior (SpatialEnvelope.clip M.plane (-level))).Nonempty)

include captured

/-- The actual compatible finite roof has exactly the original whole envelope everywhere. -/
theorem compatibleMeshRoofHeight_eq_whole (p : Plane) :
    (Q).roofHeight p = SpatialEnvelope.height M.plane p :=
  (T).toTriangulation.roofHeight_eq_whole_height conforming inside captured p

/-- Physical completion preserves the actual whole roof over any requested compact region,
including comparison connectors and fillings lying outside the original finite clip. -/
theorem exists_compatibleMesh_completion_preserving_whole_roof
    {φ : ℝ} (tilt_positive : 0 < φ) (tilt_small : φ < Real.pi / 2)
    {region : Set Plane} (region_compact : IsCompact region)
    {J : Type} [Finite J] (extra : J → Plane →ᵃ[ℝ] ℝ) (proper : ∀ j, extra j ≠ 0) :
    ∃ E : (Q).CompletionMesh φ region ((Q).combinedCompletionEquations extra),
      ∀ p ∈ region,
        SpatialEnvelope.height ((Q).completionPlanes E.tentHeight (Real.sin φ / 2)) p =
          SpatialEnvelope.height M.plane p := by
  obtain ⟨E, preserved⟩ := (Q).exists_combined_completion extra tilt_positive tilt_small
    region_compact proper
  refine ⟨E, fun p member => (preserved p member).trans ?_⟩
  exact K.compatibleMeshRoofHeight_eq_whole compact nonempty R no_boundary M positive inner_disk
    W level higher captured p

end Unfoldings.ConvexRoof
