module

public import Unfoldings.FewestNets.ThreeExitContourTails
public import Unfoldings.Geometry.PolygonalRayOrderedTransfer
public import Unfoldings.Roof.OriginalCutLabels

/-! The exact physical bank is injective, using the interpolated forest rank and the affine window. -/

@[expose] public section

noncomputable section

open scoped NNReal

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

local instance sourceOrderIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
    Fintype (T[h]).Index := @Fintype.ofFinite _ (T[h]).finite

local notation "LengthAt[" h "," c "," e "]" =>
  TriangleComplex.positiveContourBankLength D[h] Sel[h] c e
local notation "BankAt[" h "," c "," s "," e "]" =>
  PotentialCutForest.contourSourceBankChain F[h] c s e
local notation "PathAt[" h "," c "," s "," e "]" =>
  PotentialCutForest.contourSourceSpatialRay F[h] c s e
local notation "ProjectionAt[" h "," c "," s "," e "]" =>
  SpatialFolding.projectedBoundaryChain (ConvexRoof.folding Q[h]) BankAt[h,c,s,e]

/-- The actual spatial chain and the projected chain use the same affine parameters. -/
theorem horizontal_contourSourceSpatialRay_point
    (higher : ∀ v : V, (G).height (pointOf v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots)
    (event : (D[higher]).PositiveContourSource Sel[higher] contour)
    (i : Fin (LengthAt[higher,contour,event] + 1)) (t : unitInterval) :
    Cap.horizontal ((PathAt[higher,contour,starts,event]).chain.point i t) = (ProjectionAt[higher,contour,starts,event]).point i t := by
  rw [(Q[higher]).folding.projectedBoundaryChain_point BankAt[higher,contour,starts,event] i t]
  exact congrArg Cap.horizontal ((Q[higher]).folding.boundarySpatialChain_point BankAt[higher,contour,starts,event] i t)

/-- Interior bank points increase the affine-interpolated forest rank
along each closed finite link, including its endpoints. -/
theorem contourSourceSpatialRay_strictRank
    (higher : ∀ v : V, (G).height (pointOf v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots)
    (event : (D[higher]).PositiveContourSource Sel[higher] contour)
    (i : Fin (LengthAt[higher,contour,event] + 1)) :
    StrictMono ((Rank[higher]) ∘ Cap.horizontal ∘ (PathAt[higher,contour,starts,event]).chain.point i) := by
  obtain ⟨segment⟩ := R.contourSourceBankChain_aligned level M higher contour starts event i
  let first := (Forest[higher]).vertex segment.edge.val
  let last := (Forest[higher]).vertex (R.truncatedParents.parent segment.edge.val)
  let param (t : unitInterval) := (1 - t.val) * segment.first + t.val * segment.last
  have at_point (t : unitInterval) :
      (ProjectionAt[higher,contour,starts,event]).point i t = AffineMap.lineMap first last (param t) := by
    rw [PolygonalChain.point]
    refine (congrArg₂ (fun x y : Plane => AffineMap.lineMap x y t.val)
      segment.at_first.symm segment.at_last.symm).trans ?_
    change AffineMap.lineMap (AffineMap.lineMap first last segment.first)
      (AffineMap.lineMap first last segment.last) t.val = AffineMap.lineMap first last (param t)
    simp only [param, AffineMap.lineMap_apply_module']
    module
  have param_mem (t : unitInterval) : param t ∈ Set.Icc (0 : ℝ) 1 :=
    (convex_Icc 0 1) segment.first_mem segment.last_mem
      (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel _ _)
  intro s t earlier
  have up : s.val < t.val := earlier
  have growth : param s < param t := by
    dsimp only [param]
    nlinarith only [mul_pos (sub_pos.mpr up) (sub_pos.mpr segment.increasing)]
  change (Rank[higher]) (Cap.horizontal ((PathAt[higher,contour,starts,event]).chain.point i s)) <
    (Rank[higher]) (Cap.horizontal ((PathAt[higher,contour,starts,event]).chain.point i t))
  rw [R.horizontal_contourSourceSpatialRay_point level M higher contour starts event i s,
    R.horizontal_contourSourceSpatialRay_point level M higher contour starts event i t, at_point, at_point]
  exact (R.truncatedEmbedding_straight level higher).interpolatedRank_strict segment.edge
    (R.truncatedParents.ascending segment.edge.val segment.edge.property)
      (param_mem s) (param_mem t) growth

/-- All actual finite source-bank points lie at or below the chosen affine rim. -/
theorem contourSourceSpatialRay_finite_height_le
    (higher : ∀ v : V, (G).height (pointOf v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots)
    (event : (D[higher]).PositiveContourSource Sel[higher] contour)
    (i : Fin (LengthAt[higher,contour,event] + 1)) (t : unitInterval) :
    (G).height (Cap.horizontal ((PathAt[higher,contour,starts,event]).chain.point i t)) ≤ level := by
  rw [R.horizontal_contourSourceSpatialRay_point, PolygonalChain.point,
    (F[higher]).contourSourceBankChain_projected_vertex contour starts event,
    (F[higher]).contourSourceBankChain_projected_vertex contour starts event]
  let source := (D[higher]).positiveContourVertex Sel[higher] contour event
  have mem := (Q[higher]).convex_projection.lineMap_mem
    ((Q[higher]).projectedVertex_mem_footprint ((F[higher]).parents.parent^[i.castSucc.val] source))
    ((Q[higher]).projectedVertex_mem_footprint ((F[higher]).parents.parent^[i.succ.val] source))
    t.property
  change _ ∈ (Q[higher]).footprint at mem
  rw [(T[higher]).roof_footprint, M.clipAbove_referenceFloor_eq] at mem
  exact mem

/-- A strictly positive physical continuation lies above every finite
bank point, including the entire closed artificial rim. -/
theorem contourSourceSpatialRay_tail_height_gt
    (higher : ∀ v : V, (G).height (pointOf v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots)
    (event : (D[higher]).PositiveContourSource Sel[higher] contour)
    (s : ℝ≥0) (positive : 0 < s) :
    level < (G).height (Cap.horizontal ((PathAt[higher,contour,starts,event]).tail s)) := by
  obtain ⟨r, first, nonnegative, before, tail⟩ :=
    R.contourSource_physical_tail level M higher contour starts event
  let root := R.exitRoot r
  let τ := R.exits.timeAtLevel level root
  let u := τ + s.val * (τ - first)
  have τ_pos : 0 < τ := nonnegative.trans_lt before
  have later : τ < u := lt_add_of_pos_right _ (mul_pos positive (sub_pos.mpr before))
  have rim := R.exits.pointAtLevel_height level root (R.exit_origin_below level higher r)
  rw [SlopeEnvelope.ExteriorPlan.pointAtLevel, R.exits.height_ray root τ_pos.le] at rim
  rw [tail, SpatialEnvelope.horizontal_point]
  change level < (G).height (R.exits.ray root u)
  rw [R.exits.height_ray root (τ_pos.trans later).le]
  exact rim.symm.trans_lt (add_lt_add_right
    (mul_lt_mul_of_pos_right later (R.exits.positive root)) ((G).height (R.exits.point root)))

/-- The physical path is an injective target for the bank's address map,
even though its unshifted height can decrease on some links. -/
theorem contourSourceSpatialRay_mapCarrier_injective
    (higher : ∀ v : V, (G).height (pointOf v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots)
    (event : (D[higher]).PositiveContourSource Sel[higher] contour)
    (source : PolygonalRay ℂ (LengthAt[higher,contour,event] + 1)) (outward : source.Outward)
    (genuine : ∀ i, source.chain.edge i ≠ 0) (source_ne : source.direction ≠ 0) :
    Function.Injective (source.mapCarrier (PathAt[higher,contour,starts,event])) :=
  source.mapCarrier_injective_of_ordered outward genuine source_ne (PathAt[higher,contour,starts,event])
    ((Rank[higher]) ∘ Cap.horizontal)
    (R.contourSourceSpatialRay_strictRank level M higher contour starts event)
    ((F[higher]).contourSourceSpatialRay_direction_ne_zero contour starts event)
    (fun i t s pos equal =>
      ((R.contourSourceSpatialRay_tail_height_gt level M higher contour starts event s pos).not_ge
        (equal ▸ R.contourSourceSpatialRay_finite_height_le level M higher contour starts event i t)))

end Unfoldings.ConvexRoof.ThreeExitComponentRouting
