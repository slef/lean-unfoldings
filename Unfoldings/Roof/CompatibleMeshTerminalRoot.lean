module

public import Unfoldings.Roof.CompatibleMeshHistoryGeometry
public import Unfoldings.Roof.PotentialCutOrbit
public import Unfoldings.Roof.TruncatedBoundaryRoots

/-! Actual nonempty fine histories end at uniquely named original terminal points. -/

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

local instance compatibleTerminalRootIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

/-- Every nonempty original fine history reaches one uniquely named original terminal ray.
The actual root is a used rim vertex; unused isolated flat roots cannot occur. -/
theorem existsUnique_compatibleMesh_terminal_root
    (start : (T).pairedComplex.Vertex Set.univ)
    (nontrivial : 0 < (Fcut).parents.distanceToRoot start) :
    ∃! r : {v // v ∈ R.parents.roots},
      (Q).projectedVertex ((Fcut).parents.root start) = R.terminalPoint level r := by
  have on_cut := (Fcut).root_mem_cuts start nontrivial
  have on_rim := ((Q).projectedVertex_mem_frontier_iff ((Fcut).parents.root start)).mpr
    ((Fcut).root_isBoundaryVertex start nontrivial)
  rw [(T).toTriangulation.roof_footprint conforming inside, M.clip_eq_sublevel, neg_neg] at on_rim
  exact K.existsUnique_terminalPoint_of_mem_truncatedCarrier_frontier compact nonempty R no_boundary
    level higher on_cut on_rim

/-- The original terminal ray selected by the actual fine path, with no endpoint match supplied. -/
def compatibleMeshTerminalRoot (start : (T).pairedComplex.Vertex Set.univ)
    (nontrivial : 0 < (Fcut).parents.distanceToRoot start) : {v // v ∈ R.parents.roots} :=
  (K.existsUnique_compatibleMesh_terminal_root compact nonempty R no_boundary level higher M
    positive inner_disk beta acute start nontrivial).choose

/-- The constructed terminal root retains the exact original projected rim point. -/
theorem compatibleMeshTerminalRoot_point (start : (T).pairedComplex.Vertex Set.univ)
    (nontrivial : 0 < (Fcut).parents.distanceToRoot start) :
    (Q).projectedVertex ((Fcut).parents.root start) =
      R.terminalPoint level (K.compatibleMeshTerminalRoot compact nonempty R no_boundary level
        higher M
        positive inner_disk beta acute start nontrivial) :=
  (K.existsUnique_compatibleMesh_terminal_root compact nonempty R no_boundary level higher M
    positive inner_disk beta acute start nontrivial).choose_spec.1

/-- The final vertex of the actual full fine history is the exact original terminal point. -/
theorem compatibleMeshHistory_last_terminalPoint
    (start : (T).pairedComplex.Vertex Set.univ) (n : ℕ) (positive_length : 0 < n)
    (length : (Fcut).parents.distanceToRoot start = n) :
    (K.compatibleMeshHistory compact nonempty R no_boundary level higher M positive inner_disk
      beta acute start n).vertex (Fin.last n) =
        R.terminalPoint level (K.compatibleMeshTerminalRoot compact nonempty R no_boundary level
          higher M positive inner_disk beta acute start (by omega)) := by
  change (Q).projectedVertex ((Fcut).parents.parent^[n] start) = _
  have last := (congrArg (fun k : ℕ => (Fcut).parents.parent^[k] start) length.symm).trans
    ((Fcut).parents.iterate_distanceToRoot_eq_root start)
  exact (congrArg (Q).projectedVertex last).trans
    (K.compatibleMeshTerminalRoot_point compact nonempty R no_boundary level higher M positive
      inner_disk beta acute start (by omega))

end Unfoldings.ConvexRoof
