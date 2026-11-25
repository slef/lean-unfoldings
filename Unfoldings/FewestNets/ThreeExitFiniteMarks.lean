module

public import Unfoldings.FewestNets.ThreeExitMeshWindow
public import Unfoldings.Geometry.SpatialEnvelopeWindowFiber
public import Unfoldings.Complex.ContourParentBankUniqueness
public import Unfoldings.Complex.DirectedBoundaryPathGeometry
public import Unfoldings.Polyhedron.ContourParentBankMetric

/-! Original finite contour marks preserve their literal positions and intrinsic edge lengths. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel

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

local notation "T[" higher "]" => R.fineMesh level M higher
local notation "D[" higher "]" => SpatialEnvelope.FloorMesh.pairedComplex (T[higher])
local notation "F[" higher "]" => R.fineMeshForest level M higher
local notation "Sel[" higher "]" => PotentialCutForest.selection (F[higher])

local instance finiteMarksIndexFintype (higher : ∀ v : V, (G).height (pointOf v) < level) :
    Fintype (T[higher]).Index := @Fintype.ofFinite _ (T[higher]).finite

/-- The finite bank is included with all distances along its original
straight link, even at either endpoint. -/
theorem fineMeshWholeMap_edist_bank (higher : ∀ v : V, (G).height (pointOf v) < level)
    (bank : (D[higher]).BoundaryEnd (F[higher]).retain) (s t : unitInterval) :
    edist (L.fineMeshWholeMap higher ((D[higher]).directedBoundaryPath bank s))
      (L.fineMeshWholeMap higher ((D[higher]).directedBoundaryPath bank t)) =
        edist ((D[higher]).directedBoundaryPath bank s)
          ((D[higher]).directedBoundaryPath bank t) := by
  apply le_antisymm
  · exact (L.fineMeshWholeMap_lipschitz higher _ _).trans_eq (one_mul _)
  · rw [(T[higher]).pairedFolding.edist_directedBoundaryPath_eq_spatial]
    have lower := (PolygonalPoint.ambient_lipschitz.comp
      (L.whole.partition.restoreCut_lipschitz R.wholeCarrier))
      (L.fineMeshWholeMap higher ((D[higher]).directedBoundaryPath bank s))
      (L.fineMeshWholeMap higher ((D[higher]).directedBoundaryPath bank t))
    simpa only [Function.comp_apply, ENNReal.coe_one, one_mul, L.restore_fineMeshWholeMap] using lower

/-- The actual finite bank marks retain the contour-selected physical copies. -/
def contourParentMark (higher : ∀ v : V, (G).height (pointOf v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots)
    (v : (D[higher]).Vertex Set.univ) (nonroot : v ∉ (F[higher]).parents.roots)
    (side : Bool) (t : unitInterval) : L.whole.Cut :=
  L.fineMeshWholeMap higher ((D[higher]).directedBoundaryPath
    ((D[higher]).contourParentBank Sel[higher] contour (F[higher]).boundary_roots
      starts v nonroot side) t)

/-- Both whole-cut copies of one original finite bank have the same metric. -/
theorem edist_contourParentMark_sides (higher : ∀ v : V, (G).height (pointOf v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots)
    (v : (D[higher]).Vertex Set.univ) (nonroot : v ∉ (F[higher]).parents.roots)
    (s t : unitInterval) :
    edist (L.contourParentMark higher contour starts v nonroot false s)
      (L.contourParentMark higher contour starts v nonroot false t) =
    edist (L.contourParentMark higher contour starts v nonroot true s)
      (L.contourParentMark higher contour starts v nonroot true t) := by
  let bank := (D[higher]).contourParentBank Sel[higher] contour (F[higher]).boundary_roots
    starts v nonroot
  exact (L.fineMeshWholeMap_edist_bank higher (bank false) s t).trans
    (((T[higher]).pairedFolding.edist_contourParentBank_sides Sel[higher] contour
      (F[higher]).boundary_roots starts v nonroot s t).trans
      (L.fineMeshWholeMap_edist_bank higher (bank true) s t).symm)

/-- Bank paths are continuous in the complete physical cut. -/
theorem continuous_contourParentMark (higher : ∀ v : V, (G).height (pointOf v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots)
    (v : (D[higher]).Vertex Set.univ) (nonroot : v ∉ (F[higher]).parents.roots) (side : Bool) :
    Continuous (L.contourParentMark higher contour starts v nonroot side) :=
  (L.fineMeshWholeMap_lipschitz higher).continuous.comp
    ((D[higher]).continuous_directedBoundaryPath _)

local notation "Q[" h "]" => SpatialEnvelope.FloorMesh.roof (T[h])
  (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M h)

/-- The projected finite mark is exactly the affine point on its original edge. -/
theorem horizontal_contourParentMark (higher : ∀ v : V, (G).height (pointOf v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots)
    (v : (D[higher]).Vertex Set.univ) (nonroot : v ∉ (F[higher]).parents.roots)
    (side : Bool) (t : unitInterval) :
    Cap.horizontal (L.whole.partition.restoreCut R.wholeCarrier
      (L.contourParentMark higher contour starts v nonroot side t)).val =
        AffineMap.lineMap ((Q[higher]).projectedVertex v)
          ((Q[higher]).projectedVertex ((F[higher]).parents.parent v)) t.val := by
  unfold contourParentMark
  rw [L.restore_fineMeshWholeMap]
  exact (congrArg Cap.horizontal ((T[higher]).pairedFolding.contourParentBank_position
    Sel[higher] contour (F[higher]).boundary_roots starts v nonroot side t)).trans
      (Cap.horizontal.toAffineMap.apply_lineMap _ _ _)

/-- A mark strictly inside the window keeps its full finite metric fiber. -/
theorem fineMeshWholeMap_injective_at
    (higher : ∀ v : V, (G).height (pointOf v) < level)
    (x y : (D[higher]).Realization (F[higher]).retain)
    (inside : (G).height (Cap.horizontal (L.whole.partition.restoreCut R.wholeCarrier
      (L.fineMeshWholeMap higher x)).val) < level)
    (equal : L.fineMeshWholeMap higher x = L.fineMeshWholeMap higher y) : x = y := by
  apply (L.fineMeshWindowEquiv higher).injective
  exact L.whole.partition.windowCutMap_injective_at (floorWindowEquation (B := B) level M)
    L.signs L.aligned R.wholeCarrier (L.fineMeshWindowEquiv higher x)
    (floorWindow_positive level M inside) (L.fineMeshWindowEquiv higher y) equal

/-- Distinct finite banks stay distinct at an interior parameter in the strict window. -/
theorem contourParentMark_ne_of_inside
    (higher : ∀ v : V, (G).height (pointOf v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots)
    (v : (D[higher]).Vertex Set.univ) (nonroot : v ∉ (F[higher]).parents.roots)
    (t : unitInterval) (bounds : 0 < t ∧ t < 1)
    (inside : (G).height (Cap.horizontal (L.whole.partition.restoreCut R.wholeCarrier
      (L.contourParentMark higher contour starts v nonroot false t)).val) < level) :
    L.contourParentMark higher contour starts v nonroot false t ≠
      L.contourParentMark higher contour starts v nonroot true t := by
  intro equal
  let child : {v : (D[higher]).Vertex Set.univ // v ∉ (F[higher]).parents.roots} := ⟨v, nonroot⟩
  have fine := L.fineMeshWholeMap_injective_at higher _ _ inside equal
  have labels := (D[higher]).contourParentBank_parameters_eq_of_path_eq Sel[higher]
    contour (F[higher]).boundary_roots starts child child false true t t bounds fine.symm
  cases congrArg (fun p => p.2.1) labels

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
