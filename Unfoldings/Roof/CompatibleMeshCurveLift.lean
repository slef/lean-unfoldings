module

public import Unfoldings.Roof.CompatibleMeshInteriorFiber
public import Unfoldings.Metric.LocalIsometricLift

/-! Canonical finite lifts preserve whole-curve metric bounds below the completion height. -/

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

local instance compatibleCurveLiftIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "B" => SlopeEnvelope.boundaryEnvelope
  (K.clippedExtension slopes compact nonempty) boundary
local notation "Gcut" => K.truncatedCutEmbedding compact nonempty R no_boundary level higher


local notation "V" => R.levelWindowModel M level higher
local notation "proper" => R.levelWindow_proper M level higher
local notation "full" => R.levelWindow_full M level higher
local notation "domain" => SpatialEnvelope.levelEquation_domain M.plane (-level)
local notation "heights" => (Set.eqOn_refl (SpatialEnvelope.height M.plane) _)
local notation "outside" => K.compatibleMesh_cut_disjoint_interior compact nonempty R
  no_boundary level higher M positive inner_disk
local notation "removed" => K.compatibleMesh_removed_edge compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "retained" => K.compatibleMesh_retained_open_edge compact nonempty R no_boundary
  level higher M positive inner_disk beta acute

variable (W : R.WholeCutModel M)

local instance compatibleCurveLiftWholeFintype : Fintype W.Index := W.finiteIndex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Set E)
  (g : s → W.Cut)
  (below : ∀ t, (K.clippedExtension slopes compact nonempty).height
    (Cap.horizontal (W.partition.restoreCut R.carrier (g t)).val) < level)

/-- The actual uniquely determined finite lift of an entire interior curve. -/
def compatibleMeshCurveLift : s → (T).pairedComplex.Realization (Fcut).retain :=
  fun t => K.compatibleMeshLift compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W (g t) (below t)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem compatibleMeshWholeMap_curveLift (t : s) :
    K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W
      (K.compatibleMeshCurveLift compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W s g below t) = g t :=
  K.compatibleMeshWholeMap_lift compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W (g t) (below t)

/-- On a convex parameter domain the canonical finite lift keeps the original curve's
Lipschitz constant. Whole metric charts and the entire-fiber uniqueness are constructed. -/
theorem compatibleMeshCurveLift_lipschitz (convex : Convex ℝ s) {c : ℝ≥0}
    (bounded : LipschitzWith c g) : LipschitzWith c
    (K.compatibleMeshCurveLift compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W s g below) := by
  let f := K.compatibleMeshCurveLift compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W s g below
  let F := K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W
  apply lipschitzWith_lift_of_ball_charts s convex f g F c bounded
  · intro t x image
    exact K.compatibleMeshLift_unique compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W (g t) (below t) x image
  · intro t
    obtain ⟨z, image, r, rpos, chart, agrees⟩ := K.exists_compatibleMesh_ball_chart compact
      nonempty R no_boundary level higher M positive inner_disk beta acute W (g t) (below t)
    have same : z = f t := K.compatibleMeshLift_unique compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W (g t) (below t) z image
    subst z
    exact ⟨r, rpos, chart, agrees⟩

end Unfoldings.ConvexRoof
