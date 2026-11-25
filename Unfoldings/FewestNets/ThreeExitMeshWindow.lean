module

public import Unfoldings.FewestNets.ThreeExitFineCut
public import Unfoldings.Geometry.SpatialEnvelopeWindowPartition
public import Unfoldings.Geometry.SpatialGraphCutIndependence
public import Unfoldings.Geometry.SpatialGraphPresentations
public import Unfoldings.Metric.LocalChartSourceTransport

/-! Transfer finite contour charts to one actual whole cut aligned with the slanted floor. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : FewestNets.ThreeExitStemWindows}
  (R : K.ThreeExitComponentRouting seed B compact nonempty H)

local notation "U" => K.selectionComponent slopes seed
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ K.restrictedCarrier U}
local notation "p" => (fun v : V => K.projectedVertex (Subtype.val v))
local notation "G₀" => K.componentClippedExtension
  (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty
local notation "G" => SlopeEnvelope.recenter (G₀) B.reference
local notation "floor" => SlopeEnvelope.FiniteSlopeModel.referenceFloor B.reference

variable (level : ℝ)
  (M : (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty).FiniteSlopeModel)

local notation "T[" higher "]" => R.fineMesh level M higher
local notation "F[" higher "]" => R.fineMeshForest level M higher
local notation "footprint" => SpatialEnvelope.clipAbove M.plane floor (-level)

local instance windowVertexFintype : Fintype V := Fintype.ofFinite _
local instance windowMeshIndexFintype (higher : ∀ v : V, (G).height (p v) < level) :
    Fintype (T[higher]).Index := @Fintype.ofFinite _ (T[higher]).finite

/-- Each original support compared with the floor defines one window inequality. -/
def floorWindowEquation (i : M.Face) : Plane →ᵃ[ℝ] ℝ :=
  (M.plane i).height - floor - AffineMap.const ℝ Plane (-level)

local notation "eqns" => floorWindowEquation (B := B) level M
/-- The window represented by all the original affine support inequalities. -/
def floorWindowRegion : Set Plane := {x | ∀ i, 0 ≤ (eqns) i x}

local notation "region" => floorWindowRegion (B := B) level M

theorem floorWindow_domain : region = footprint := by
  ext x
  rw [SpatialEnvelope.mem_clipAbove_iff]
  constructor
  · intro h
    obtain ⟨i, active⟩ := AffineEnvelope.exists_height_eq (fun j => (M.plane j).height) x
    have lower : 0 ≤ (M.plane i).height x - floor x - (-level) := h i
    change SpatialEnvelope.height M.plane x = (M.plane i).height x at active
    rw [active]
    linarith only [lower]
  · intro lower i
    have upper : SpatialEnvelope.height M.plane x ≤ (M.plane i).height x :=
      AffineEnvelope.height_le (fun j => (M.plane j).height) x i
    change 0 ≤ (M.plane i).height x - floor x - (-level)
    linarith only [lower, upper]

theorem floorWindow_positive {x : Plane}
    (strict : (G).height x < level) (i : M.Face) : 0 < (eqns) i x := by
  have upper := AffineEnvelope.height_le (fun j => (M.plane j).height) x i
  change SpatialEnvelope.height M.plane x ≤ _ at upper
  rw [M.height_eq] at upper
  rw [SlopeEnvelope.recenter_height] at strict
  change 0 < (M.plane i).height x - floor x - (-level)
  rw [SlopeEnvelope.FiniteSlopeModel.referenceFloor_apply]
  linarith only [upper, strict]

theorem floorWindow_proper (higher : ∀ v : V, (G).height (p v) < level) (i : M.Face) :
    (eqns) i ≠ 0 := by
  let q := p (meshInteriorVertex (K := K) (slopes := slopes) (seed := seed))
  have positive : 0 < (eqns) i q := floorWindow_positive level M
    (higher (meshInteriorVertex (K := K) (slopes := slopes) (seed := seed))) i
  intro zero
  have evaluation := DFunLike.congr_fun zero q
  exact positive.ne' evaluation

theorem floorWindow_full (higher : ∀ v : V, (G).height (p v) < level) :
    (interior region).Nonempty := by
  rw [floorWindow_domain]
  exact meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M higher

/-- The same finite partition records both the original cut lines and the true floor sides. -/
structure FloorWindowModel where
  whole : R.WholeCutModel M
  signs : whole.Index → M.Face → Bool
  aligned : ∀ a x, x ∈ whole.partition.footprint a → ∀ i,
    0 ≤ AffineArrangement.signed ((eqns) i) (signs a i) x

/-- Construct the whole physical model with its original floor window identified. -/
def floorWindowModel (higher : ∀ v : V, (G).height (p v) < level) : R.FloorWindowModel level M :=
  Classical.choice (by
    let extra := Sum.elim R.wholeCutEquation eqns
    have proper : ∀ i, extra i ≠ 0 := Sum.rec R.wholeCutEquation_ne_zero
      (floorWindow_proper level M higher)
    obtain ⟨A, finite, P, signs, aligned⟩ := SpatialEnvelope.exists_wholePartition M.plane extra proper
    let W : R.WholeCutModel M := ⟨A, finite, P, (fun a i => signs a (.inl i)),
      (fun a x hx i => aligned a x hx (.inl i))⟩
    exact ⟨⟨W, (fun a i => signs a (.inr i)), (fun a x hx i => aligned a x hx (.inr i))⟩⟩)

namespace FloorWindowModel

variable {R level M} (L : R.FloorWindowModel level M)

theorem window_disjoint_wholeCut_interior
    (i : {i : L.whole.Index // SpatialEnvelope.WholePartition.WindowSelected L.signs i}) :
    Disjoint (interior (L.whole.partition.footprint i.val)) R.wholeCarrier := by
  apply Set.disjoint_left.mpr
  intro x inside cut
  obtain ⟨j, zero⟩ := R.wholeCarrier_covered_by_equations cut
  exact not_mem_interior_of_affine_lower_bound
    (AffineArrangement.signed (R.wholeCutEquation j) (L.whole.signs i.val j))
    (AffineArrangement.signed_ne_zero _ (R.wholeCutEquation_ne_zero j) _)
    (fun z hz => L.whole.aligned i.val z hz j)
    ((AffineArrangement.signed_eq_zero_iff _ _ _).mpr zero) inside

local notation "MeshPatch[" higher "]" => SpatialGraphPartition.withRegion
  (SpatialEnvelope.FloorMesh.graphPartition (T[higher])) region (floorWindow_domain (B := B) level M)
local notation "WindowPatch[" higher "]" => (SpatialEnvelope.WholePartition.windowGraphPartition L.whole.partition eqns
  (floorWindow_proper (B := B) level M higher) L.signs L.aligned (floorWindow_full (B := B) level M higher))

/-- The triangulated finite forest cut is the very same metric as the
closed window subfamily of the complete physical cut. -/
def fineMeshWindowEquiv (higher : ∀ v : V, (G).height (p v) < level) :
    (T[higher]).pairedComplex.Realization (F[higher]).retain ≃ᵢ
      L.whole.partition.WindowCut L.signs R.wholeCarrier :=
  (R.fineMeshWholeGraphEquiv level M higher).trans
    ((MeshPatch[higher]).cutPartitionEquiv (WindowPatch[higher]) R.wholeCarrier
      R.isClosed_wholeCarrier (R.fineMesh_disjoint_wholeCut_interior level M higher)
      L.window_disjoint_wholeCut_interior)

theorem fold_fineMeshWindowEquiv (higher : ∀ v : V, (G).height (p v) < level)
    (x : (T[higher]).pairedComplex.Realization (F[higher]).retain) :
    (WindowPatch[higher]).fold R.wholeCarrier (L.fineMeshWindowEquiv higher x) =
      (T[higher]).pairedFolding.toSpace (F[higher]).retain x :=
  ((MeshPatch[higher]).fold_cutPartitionEquiv (WindowPatch[higher]) R.wholeCarrier
    R.isClosed_wholeCarrier (R.fineMesh_disjoint_wholeCut_interior level M higher)
    L.window_disjoint_wholeCut_interior (R.fineMeshWholeGraphEquiv level M higher x)).trans
      (R.fold_fineMeshWholeGraphEquiv level M higher x)

/-- Include the exact finite mesh cut in this complete physical cut. -/
def fineMeshWholeMap (higher : ∀ v : V, (G).height (p v) < level)
    (x : (T[higher]).pairedComplex.Realization (F[higher]).retain) : L.whole.Cut :=
  L.whole.partition.windowCutMap L.signs R.wholeCarrier (L.fineMeshWindowEquiv higher x)

theorem restore_fineMeshWholeMap (higher : ∀ v : V, (G).height (p v) < level)
    (x : (T[higher]).pairedComplex.Realization (F[higher]).retain) :
    (L.whole.partition.restoreCut R.wholeCarrier (L.fineMeshWholeMap higher x)).val =
      (T[higher]).pairedFolding.toSpace (F[higher]).retain x :=
  (L.whole.partition.restoreCut_windowCutMap L.signs R.wholeCarrier _).trans (L.fold_fineMeshWindowEquiv higher x)

theorem fineMeshWholeMap_lipschitz (higher : ∀ v : V, (G).height (p v) < level) :
    LipschitzWith 1 (L.fineMeshWholeMap higher) := by
  change LipschitzWith 1 (L.whole.partition.windowCutMap L.signs R.wholeCarrier ∘
    (L.fineMeshWindowEquiv higher))
  simpa only [mul_one] using (L.whole.partition.windowCutMap_lipschitz L.signs R.wholeCarrier).comp
    (L.fineMeshWindowEquiv higher).isometry.lipschitzWith

/-- Each whole-cut copy over the strict affine window has a whole
isometric neighborhood in the exact finite contour cut. -/
theorem exists_fineMesh_ball_chart (higher : ∀ v : V, (G).height (p v) < level)
    (x : L.whole.Cut)
    (inside : (G).height (Cap.horizontal (L.whole.partition.restoreCut R.wholeCarrier x).val) < level) :
    ∃ y : (T[higher]).pairedComplex.Realization (F[higher]).retain,
      L.fineMeshWholeMap higher y = x ∧ ∃ r > 0,
      ∃ chart : Metric.eball y (ENNReal.ofReal r) ≃ᵢ Metric.eball x (ENNReal.ofReal r),
        ∀ z, (chart z).val = L.fineMeshWholeMap higher z.val :=
  exists_ball_chart_isometry_source (L.fineMeshWindowEquiv higher).symm
    (L.whole.partition.windowCutMap L.signs R.wholeCarrier) x
    (L.whole.partition.exists_windowCut_ball_chart eqns L.signs L.aligned R.wholeCarrier x
      (floorWindow_positive level M inside))

end FloorWindowModel
end Unfoldings.ConvexRoof.ThreeExitComponentRouting
