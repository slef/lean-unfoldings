module

public import Unfoldings.Roof.CompatibleContourParentMarkCharts
public import Unfoldings.Geometry.DirectedEdgeHalfPlaneFrame
public import Unfoldings.Complex.BoundaryBankLength
public import Unfoldings.Metric.CenteredBallChartRestriction

/-! Directed half-plane coordinates on actual original finite roof banks. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof

open MetricGluing

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

local instance contourParentNormalizedMeshFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
variable (contour :
    (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.BoundaryContour
    ((K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.selectedRetain
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection))
  (starts : (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.contourOriginalVertex
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour 0 ∈
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).parents.roots)
  (W : R.WholeCutModel M)

local instance contourParentNormalizedWholeFintype : Fintype W.Index := W.finiteIndex

local notation "ParentAt[" v "," h "," side "," t "]" => K.compatibleContourParentMark compact
  nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W v h side t

local notation "ParentBank[" v "," h "," side "]" => TriangleComplex.contourParentBank D Selection
  contour (PotentialCutForest.boundary_roots Fcut) starts v h side
local notation "RawBank[" v "," h "," side "]" => Prod.fst
  (TriangleComplex.boundaryEndEquiv D (PotentialCutForest.retain Fcut) ParentBank[v,h,side])
local notation "Flag[" v "," h "," side "]" => Prod.snd
  (TriangleComplex.boundaryEndEquiv D (PotentialCutForest.retain Fcut) ParentBank[v,h,side])
local notation "PointAt[" v "," h "," side "," t "]" => TriangleComplex.bankParameterFromEnd D
  RawBank[v,h,side] Flag[v,h,side] t
/-- The actual parent bank has centered rigid half-plane coordinates at its original
arclength speed, with either prescribed occupied half-plane. -/
theorem compatibleContourParentMark_normalized_chart
    (vertex : (D).Vertex Set.univ) (nonroot : vertex ∉ (Fcut).parents.roots)
    (side occupied : Bool) (t : unitInterval) (bounds : 0 < t ∧ t < 1) :
    ∃ r, Nonempty (BankHalfPlaneChart (ParentAt[vertex,nonroot,side,·]) t occupied
      (fun s => (s.val - t.val) * (D).boundaryBankLength ParentBank[vertex,nonroot,side]) r) := by
  let bank := RawBank[vertex,nonroot,side]
  let flag := Flag[vertex,nonroot,side]
  let triangle := (D).triangle bank.val.face
  let q := PointAt[vertex,nonroot,side,t]
  let model := triangle.edgeHalfPlanePoint bank.val.edge q
  obtain ⟨r, radius_pos, A, center, physical⟩ :=
    K.compatibleContourParentMark_halfPlane_chart compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W vertex nonroot side t bounds
  obtain ⟨F, parameter, membership⟩ :=
    triangle.exists_directedEdgeHalfPlaneFrame bank.val.edge flag occupied t
  have speed : ‖(triangle.endpoint bank.val.edge (!flag)).val -
        (triangle.endpoint bank.val.edge flag).val‖ =
      (D).boundaryBankLength ParentBank[vertex,nonroot,side] := by
    rw [(D).boundaryBankLength_eq_edge]
    change _ = dist (triangle.vertex bank.val.edge) (triangle.vertex (Triangle.next bank.val.edge))
    cases h : flag
    · exact (dist_eq_norm _ _).symm.trans (dist_comm _ _)
    · exact (dist_eq_norm _ _).symm
  have coordinates (s : unitInterval) : F (PointAt[vertex,nonroot,side,s]).val =
      (((s.val - t.val) * (D).boundaryBankLength ParentBank[vertex,nonroot,side] : ℝ) : ℂ) := by
    rw [← speed]
    exact parameter s.val
  let B := setIsometryEquiv F.toIsometryEquiv _ _ membership
  have base : B model = bankHalfPlaneOrigin occupied := by
    apply Subtype.ext
    change F q.val = 0
    simpa only [sub_self, zero_mul, Complex.ofReal_zero] using coordinates t
  refine ⟨r, ⟨⟨radius_pos, (A.trans (metricBallEBallEquiv model r)).trans
    (basedEBallIsometry B model _ base (ENNReal.ofReal r)), ?_, ?_⟩⟩⟩
  · change B (A _).val = bankHalfPlaneOrigin occupied
    rw [center, base]
  · intro s near
    change F (A _).val.val = _
    rw [K.compatibleContourParentMark_chart_parameter compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W vertex nonroot side t
      A physical s near]
    exact coordinates s

end Unfoldings.ConvexRoof
