module

public import Unfoldings.FewestNets.ThreeExitSourcePhysicalOrder
public import Unfoldings.Geometry.SourceGapPhysicalCollapse
public import Unfoldings.Geometry.SourceGapFibers

/-! Every source gap collapses properly onto its actual spatial bank. -/

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
local notation "G" => SlopeEnvelope.recenter
  (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty) B.reference
local notation "pointOf" => (fun v : V => K.projectedVertex (Subtype.val v))

variable (level : ℝ)
  (M : (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty).FiniteSlopeModel)

local notation "T[" h "]" => R.fineMesh level M h
local notation "D[" h "]" => SpatialEnvelope.FloorMesh.pairedComplex T[h]
local notation "Q[" h "]" => SpatialEnvelope.FloorMesh.roof T[h]
  (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M h)
local notation "F[" h "]" => R.fineMeshForest level M h
local notation "Sel[" h "]" => PotentialCutForest.selection F[h]
local notation "Forest[" h "]" => R.truncatedEmbedding level h
local notation "Rank[" h "]" => FiniteEmbeddedGraph.interpolatedRank (Forest[h])
  (AscendingParents.height R.truncatedParents)

local instance sourceCollapseIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
    Fintype (T[h]).Index := @Fintype.ofFinite _ (T[h]).finite

local notation "LengthAt[" h "," c "," e "]" =>
  TriangleComplex.positiveContourBankLength D[h] Sel[h] c e
local notation "BankAt[" h "," c "," s "," e "]" =>
  PotentialCutForest.contourSourceBankChain F[h] c s e
local notation "PathAt[" h "," c "," s "," e "]" =>
  PotentialCutForest.contourSourceSpatialRay F[h] c s e
local notation "SourceAt[" h "," c "," s "," e "]" =>
  PotentialCutForest.contourSourceRay F[h] c s e
local notation "OpenedAt[" h "," c "," s "," e "]" =>
  PotentialCutForest.contourSourceOpenedRay F[h] c s e

private theorem contourSourceRay_genuine
    (higher : ∀ v : V, (G).height (pointOf v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots)
    (event : (D[higher]).PositiveContourSource Sel[higher] contour)
    (i : Fin (LengthAt[higher,contour,event] + 1)) :
    (SourceAt[higher,contour,starts,event]).chain.edge i ≠ 0 :=
  (D[higher]).boundaryChainRoll_edge_ne_zero BankAt[higher,contour,starts,event] i

/-- The actual gap collapses to the original spatial chain and its true exit. -/
def contourSourceGapCollapse
    (higher : ∀ v : V, (G).height (pointOf v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots)
    (event : (D[higher]).PositiveContourSource Sel[higher] contour)
    (gap : OrientedBankGap SourceAt[higher,contour,starts,event] OpenedAt[higher,contour,starts,event])
   : PolygonalPoint gap.model.region → (PathAt[higher,contour,starts,event]).carrier :=
  gap.collapseTo (PathAt[higher,contour,starts,event])

theorem isProperMap_contourSourceGapCollapse
    (higher : ∀ v : V, (G).height (pointOf v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots)
    (event : (D[higher]).PositiveContourSource Sel[higher] contour)
    (gap : OrientedBankGap SourceAt[higher,contour,starts,event] OpenedAt[higher,contour,starts,event])
   :
    IsProperMap (R.contourSourceGapCollapse level M higher contour starts event gap) :=
  gap.isProperMap_collapseTo (PathAt[higher,contour,starts,event])
    (R.contourSourceRay_genuine level M higher contour starts event)
    ((F[higher]).contourSourceSpatialRay_direction_ne_zero contour starts event)

theorem contourSourceGapCollapse_edgePoint
    (higher : ∀ v : V, (G).height (pointOf v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots)
    (event : (D[higher]).PositiveContourSource Sel[higher] contour)
    (gap : OrientedBankGap SourceAt[higher,contour,starts,event] OpenedAt[higher,contour,starts,event])
   (side : Bool) (i : Fin (LengthAt[higher,contour,event] + 1)) (t : unitInterval) :
    (R.contourSourceGapCollapse level M higher contour starts event gap (gap.model.edgePoint side i t)).val =
      (PathAt[higher,contour,starts,event]).chain.point i t :=
  congrArg Subtype.val (gap.collapseTo_edgePoint (PathAt[higher,contour,starts,event])
    (R.contourSourceRay_genuine level M higher contour starts event) side i t)

theorem contourSourceGapCollapse_tailPoint
    (higher : ∀ v : V, (G).height (pointOf v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots)
    (event : (D[higher]).PositiveContourSource Sel[higher] contour)
    (gap : OrientedBankGap SourceAt[higher,contour,starts,event] OpenedAt[higher,contour,starts,event])
   (side : Bool) (t : ℝ≥0) :
    (R.contourSourceGapCollapse level M higher contour starts event gap (gap.model.tailPoint side t)).val =
      (PathAt[higher,contour,starts,event]).tail t :=
  congrArg Subtype.val (gap.collapseTo_tailPoint (PathAt[higher,contour,starts,event])
    (R.contourSourceRay_genuine level M higher contour starts event) side t)

/-- Every gap fiber is the exact closed arc between its original two bank
marks, with the source itself allowed to be a singleton. -/
theorem hasMarkedCollapseFibers_contourSourceGapCollapse
    (higher : ∀ v : V, (G).height (pointOf v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots)
    (event : (D[higher]).PositiveContourSource Sel[higher] contour)
    (gap : OrientedBankGap SourceAt[higher,contour,starts,event] OpenedAt[higher,contour,starts,event])
   :
    gap.model.HasMarkedCollapseFibers (PathAt[higher,contour,starts,event])
      (fun x => (R.contourSourceGapCollapse level M higher contour starts event gap x).val) :=
  gap.hasMarkedCollapseFibers_collapseTo (PathAt[higher,contour,starts,event])
    (R.contourSourceRay_genuine level M higher contour starts event)
    (R.contourSourceSpatialRay_mapCarrier_injective level M higher contour starts event
      (SourceAt[higher,contour,starts,event]) gap.first_outward (R.contourSourceRay_genuine level M higher contour starts event)
      gap.first_nonzero)

end Unfoldings.ConvexRoof.ThreeExitComponentRouting
