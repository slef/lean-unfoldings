module

public import Unfoldings.FewestNets.ThreeExitGraftPhysicalAddresses
public import Unfoldings.Boundary.HalfPlaneMetric
public import Unfoldings.Metric.RestoredPlacedBall
public import Unfoldings.Metric.BankHalfPlaneChart
public import Unfoldings.Geometry.DirectedEdgeHalfPlaneFrame

/-! Strict finite banks of the original cut have centered rigid half-plane charts. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
open MetricGluing

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : FewestNets.ThreeExitStemWindows}
  {R : K.ThreeExitComponentRouting seed B compact nonempty H}

local notation "U" => K.selectionComponent slopes seed
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ K.restrictedCarrier U}
local notation "G" => SlopeEnvelope.recenter
  (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty) B.reference
local notation "pointOf" => (fun v : V => K.projectedVertex (Subtype.val v))

variable {level : ℝ}
  {M : (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty).FiniteSlopeModel}
  (L : R.FloorWindowModel level M)

local notation "T[" h "]" => R.fineMesh level M h
local notation "D[" h "]" => SpatialEnvelope.FloorMesh.pairedComplex T[h]
local notation "F[" h "]" => R.fineMeshForest level M h
local notation "Sel[" h "]" => PotentialCutForest.selection F[h]

local instance graftFiniteBankChartIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
    Fintype (T[h]).Index := @Fintype.ofFinite _ (T[h]).finite

variable (S : SourceContour (R := R) (M := M) (level := level))

local notation "T" => T[S.higher]
local notation "D" => D[S.higher]
local notation "Fcut" => F[S.higher]
local notation "Selection" => Sel[S.higher]
local notation "Base" => contourBaseMark L S
local notation "Attachment" => PotentialCutForest.ContourAttachment Fcut
local notation "Param" => PotentialCutForest.contourAttachmentParameter Fcut

local notation "restore" =>
  SpatialEnvelope.WholePartition.restoreCut L.whole.partition R.wholeCarrier

local notation "Child" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}

set_option maxHeartbeats 1650000 in
/-- The original finite bank has a half-plane chart at its original arclength
speed. The occupied side can be chosen independently of the bank label. -/
theorem contourBaseMark_finite_halfPlaneChart (e : Child) (side occupied : Bool)
    (t : unitInterval) (strict : 0 < t ∧ t < 1) :
    ∃ speed : ℝ, 0 < speed ∧
      (∀ s u, edist (Base (.inl e) side s) (Base (.inl e) side u) =
        ENNReal.ofReal speed * edist s u) ∧
      ∃ r, Nonempty (BankHalfPlaneChart (Base (.inl e) side) t occupied
        (fun s => (s.val - t.val) * speed) r) := by
  let directed := (D).contourParentBank Selection S.contour (Fcut).boundary_roots S.starts
    e.val e.property side
  let bank := ((D).boundaryEndEquiv (Fcut).retain directed).1
  let flag := ((D).boundaryEndEquiv (Fcut).retain directed).2
  let triangle := (D).triangle bank.val.face
  let q (s : unitInterval) := (D).bankParameterFromEnd bank flag s
  let model := triangle.edgeHalfPlanePoint bank.val.edge (q t)
  let source := (D).bankMap (Fcut).retain bank (q t)
  let chart := (D).boundaryChart (Fcut).retain bank (q t)
    ((D).bankParameterFromEnd_nonvertex bank flag t strict.1 strict.2)
  let map := L.fineMeshWholeMap S.higher
  have inside : (G).height (Cap.horizontal (restore (Base (.inl e) side t)).val) < level := by
    rw [L.contourPhysicalAddress_side S]
    exact L.contourPhysicalAddress_finite_lt S e t strict
  obtain ⟨y, position, ρ, ρ_pos, Y, agrees⟩ :=
    L.exists_fineMesh_ball_chart S.higher (Base (.inl e) side t) inside
  have name : map source = Base (.inl e) side t := rfl
  have same : y = source := L.fineMeshWholeMap_injective_at S.higher y source
    (position.symm ▸ inside) (position.trans name.symm)
  subst y
  let place : triangle.edgeHalfPlane bank.val.edge → Space :=
    fun z => (T).placement bank.val.face z.val
  have embedding : Function.Injective place :=
    ((T).placement bank.val.face).injective.comp Subtype.val_injective
  obtain ⟨r, rpos, A, physical⟩ := exists_restored_placed_ball_chart map
    ((T).pairedFolding.toSpace (Fcut).retain) (fun x : L.whole.Cut => (restore x).val)
    place embedding (L.restore_fineMeshWholeMap S.higher) ρ_pos chart.positive
    Y agrees chart.halfPlaneChart ((T).pairedFolding.boundary_halfPlaneChart_physical chart)
    (show place model = (T).pairedFolding.toSpace (Fcut).retain source from rfl)
  obtain ⟨F, parameter, membership⟩ :=
    triangle.exists_directedEdgeHalfPlaneFrame bank.val.edge flag occupied t
  let speed := (D).boundaryBankLength directed
  have length : ‖(triangle.endpoint bank.val.edge (!flag)).val -
      (triangle.endpoint bank.val.edge flag).val‖ = speed := by
    unfold speed
    rw [(D).boundaryBankLength_eq_edge]
    change _ = dist (triangle.vertex bank.val.edge) (triangle.vertex (Triangle.next bank.val.edge))
    cases h : flag
    · exact (dist_eq_norm _ _).symm.trans (dist_comm _ _)
    · exact (dist_eq_norm _ _).symm
  have coordinates (s : unitInterval) : F (q s).val = (((s.val - t.val) * speed : ℝ) : ℂ) := by
    rw [← length]
    exact parameter s.val
  let E := setIsometryEquiv F.toIsometryEquiv _ _ membership
  have base : E model = bankHalfPlaneOrigin occupied := by
    apply Subtype.ext
    change F (q t).val = 0
    simpa only [sub_self, zero_mul, Complex.ofReal_zero] using coordinates t
  refine ⟨speed, (D).boundaryBankLength_pos directed, ?_, r,
    ⟨⟨rpos, (A.trans (metricBallEBallEquiv model r)).trans
      (basedEBallIsometry E model _ base (ENNReal.ofReal r)), ?_, ?_⟩⟩⟩
  · intro s u
    exact (L.fineMeshWholeMap_edist_bank S.higher directed s u).trans
      ((T).pairedFolding.edist_directedBoundaryPath_eq_length directed s u)
  · have center : (A ⟨Base (.inl e) side t, Metric.mem_eball_self
        (ENNReal.ofReal_pos.mpr rpos)⟩).val = model :=
      embedding ((physical _).trans (L.restore_fineMeshWholeMap S.higher source))
    change E (A _).val = bankHalfPlaneOrigin occupied
    exact (congrArg E center).trans base
  · intro s near
    have loc : (A ⟨Base (.inl e) side s, near⟩).val.val = (q s).val :=
      ((T).placement bank.val.face).injective ((physical _).trans
        (L.restore_fineMeshWholeMap S.higher ((D).directedBoundaryPath directed s)))
    change F (A _).val.val = _
    exact (congrArg F loc).trans (coordinates s)

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
