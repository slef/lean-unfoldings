module

public import Unfoldings.Roof.CompatibleMeshCornerCharts
public import Unfoldings.Roof.CompatibleContourFiniteGraft
public import Unfoldings.Complex.DirectedBoundaryPathReversal
public import Unfoldings.Complex.BoundaryBankLength
public import Unfoldings.Cone.DirectedIntervalChart
public import Unfoldings.Cone.MarkedSectorGerm

/-! Calibrate an original roof wedge by the two directed banks pointing away from its vertex. -/

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
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance directedRoofSectorMeshFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
variable (W : R.WholeCutModel M)

local instance directedRoofSectorWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W
local notation "Retain" => PotentialCutForest.retain Fcut
local notation "VertexAt[" w "]" => TriangleComplex.vertexPoint D Retain w
local notation "Height[" x "]" => SlopeEnvelope.height (K.clippedExtension slopes compact nonempty)
  (Cap.horizontal (SpatialFolding.toSpace
    (SpatialEnvelope.Triangulation.pairedFolding
      (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) Retain x))

/-- The actual roof chart matches both outward directed bank paths with arclength
from their common original vertex. -/
theorem compatibleMesh_directedRoofSectorGerm
    (p : (T).pairedComplex.BoundaryEnd (Fcut).retain)
    (below : Height[VertexAt[(D).boundaryEndVertex Retain p]] < level)
    (small : (D).totalAngle Retain ((D).boundaryEndVertex Retain p) < 2 * Real.pi) :
    let w := (D).boundaryEndVertex Retain p
    let bank (b : Bool) := if b then (D).boundaryMate Retain p else p
    let mark (b : Bool) (t : unitInterval) := Map ((D).directedBoundaryPath (bank b) t)
    let length (b : Bool) := (D).boundaryBankLength (bank b)
    Nonempty (MarkedSectorGerm (Map VertexAt[w]) ((D).totalAngle Retain w) mark length) := by
  let w := (D).boundaryEndVertex Retain p
  let x := Map VertexAt[w]
  let bank (b : Bool) := if b then (D).boundaryMate Retain p else p
  let mark (b : Bool) (t : unitInterval) := Map ((D).directedBoundaryPath (bank b) t)
  let length (b : Bool) := (D).boundaryBankLength (bank b)
  have center (g : (D).BoundaryEnd Retain) (h : (D).boundaryEndVertex Retain g = w) :
      Map ((D).directedBoundaryPath g 0) = x :=
    congrArg Map (((D).directedBoundaryPath_zero g).trans (congrArg ((D).vertexPoint Retain) h))
  have speeds (g : (D).BoundaryEnd Retain) (h : (D).boundaryEndVertex Retain g = w)
      (t : unitInterval) : ENNReal.ofReal (t.val * (D).boundaryBankLength g) =
        edist (Map ((D).directedBoundaryPath g t)) x := by
    rw [← center g h, K.compatibleWholeMap_edist_bank compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W g t 0,
      (T).pairedFolding.edist_directedBoundaryPath_eq_length, mul_comm t.val,
      ENNReal.ofReal_mul ((D).boundaryBankLength_pos g).le, edist_dist]
    congr 1
    apply congrArg ENNReal.ofReal
    change t.val = dist t.val 0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg t.property.1]
  obtain ⟨r, rpos, chart, first, last⟩ := (D).exists_directedIntervalChart Retain p Map
    small speeds (K.compatibleMesh_corner_fan_chart compact nonempty R no_boundary level higher
      M positive inner_disk beta acute W _ below)
  have at_w (b : Bool) : (D).boundaryEndVertex Retain (bank b) = w := by
    cases b
    · rfl
    · exact ((D).boundaryMate_spec Retain p).2
  have zero_near : edist (mark false 0) x < ENNReal.ofReal r := by
    rw [show mark false 0 = x from center p rfl, edist_self]
    exact ENNReal.ofReal_pos.mpr rpos
  have center_eq : (chart ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos)⟩).val =
      closedAngularSectorOrigin ((D).totalAngle_pos Retain w).le := by
    apply PolygonalPoint.ext
    have same : (⟨mark false 0, zero_near⟩ : Metric.eball x (ENNReal.ofReal r)) =
        ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos)⟩ := Subtype.ext (center p rfl)
    rw [← same]
    exact (first 0 zero_near).trans (by simp [closedAngularSectorOrigin])
  refine ⟨⟨⟨(D).totalAngle_pos Retain w, r, rpos, chart, center_eq⟩,
    fun b t => (speeds (bank b) (at_w b) t).symm, ?_⟩⟩
  intro b t near
  cases b
  · simpa only [bank, length, mark, Bool.false_eq_true, ite_false,
      polarRay_zero, Complex.real_smul, mul_one] using first t near
  · exact last t near

end Unfoldings.ConvexRoof
