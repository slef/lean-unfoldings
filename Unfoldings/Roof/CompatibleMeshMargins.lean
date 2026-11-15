module

public import Unfoldings.Roof.CompatibleMeshPaths
public import Unfoldings.Roof.CompatibleFineMargins

/-! Every actual fine mesh parent history inherits a uniform quantitative radial margin. -/

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

local instance compatibleMeshMarginIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

/-- The true fine history has radial progress against its true next selected edge.
No assumption says its last vertex was an original coarse vertex. -/
theorem compatibleMeshHistory_radial_margin {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
    (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)
    (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2)
    (start : (T).pairedComplex.Vertex Set.univ) (n : ℕ)
    (before : n < (Fcut).parents.distanceToRoot start) :
    Real.cos (2 * annularHistoryAngle (a / b) β) *
      (‖(Q).projectedVertex ((Fcut).parents.parent^[n] start) - (Q).projectedVertex start‖ *
        ‖(Q).projectedVertex ((Fcut).parents.parent ((Fcut).parents.parent^[n] start)) -
          (Q).projectedVertex ((Fcut).parents.parent^[n] start)‖) ≤
      inner ℝ ((Q).projectedVertex ((Fcut).parents.parent^[n] start) - (Q).projectedVertex start)
        ((Q).projectedVertex ((Fcut).parents.parent ((Fcut).parents.parent^[n] start)) -
          (Q).projectedVertex ((Fcut).parents.parent^[n] start)) := by
  let P := K.compatibleMeshHistory compact nonempty R no_boundary level higher M
    positive inner_disk beta acute start n
  have follows := K.compatibleMeshHistory_follows compact nonempty R no_boundary level higher M
    positive inner_disk beta acute start n before.le
  have next_step := K.compatibleMesh_parent_follows compact nonempty R no_boundary level higher M
    positive inner_disk beta acute ((Fcut).parents.parent^[n] start)
      ((Fcut).parents.iterate_lt_distanceToRoot_not_mem start before)
  have margin := R.follows_radial_margin_at_fine_step positive beta acute bpos ratio inner_disk
    upper small P follows
      ((Q).projectedVertex ((Fcut).parents.parent ((Fcut).parents.parent^[n] start))) next_step
  exact margin

end Unfoldings.ConvexRoof
