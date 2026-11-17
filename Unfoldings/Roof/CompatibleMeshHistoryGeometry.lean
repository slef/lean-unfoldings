module

public import Unfoldings.Roof.CompatibleMeshMargins
public import Unfoldings.Geometry.GenericRadialSource
public import Unfoldings.Roof.CompatibleSubhistoryMargins

/-! Compatible fine histories have distinct projected vertices up to their actual first root. -/

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

local instance compatibleHistoryGeometryIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

/-- The actual projected history has no repeated vertices before its first root. -/
theorem compatibleMeshHistory_vertex_injective
    (start : (T).pairedComplex.Vertex Set.univ) (n : ℕ)
    (before : n ≤ (Fcut).parents.distanceToRoot start) :
    Function.Injective (K.compatibleMeshHistory compact nonempty R no_boundary level higher M
      positive inner_disk beta acute start n).vertex := by
  intro i j same
  have original := (Q).projectedVertex_injective same
  let first : Fin ((Fcut).parents.distanceToRoot start + 1) := ⟨i.val, by omega⟩
  let last : Fin ((Fcut).parents.distanceToRoot start + 1) := ⟨j.val, by omega⟩
  have indices : first = last := ((Fcut).parents.strictMono_height_rootOrbit start).injective
    (congrArg (Fcut).parents.height original)
  have values := congrArg (fun k : Fin ((Fcut).parents.distanceToRoot start + 1) => k.val) indices
  exact Fin.ext values

end Unfoldings.ConvexRoof
