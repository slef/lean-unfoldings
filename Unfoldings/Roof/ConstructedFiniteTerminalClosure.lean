module

public import Unfoldings.Roof.ConstructedFiniteTerminalParameters
public import Unfoldings.Geometry.OrderedRayClosure
public import Unfoldings.Geometry.PolygonalClosureEquations

/-! Construct supported generic Jordan closures of actual original finite terminal banks. -/

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

local instance finiteTerminalClosureIndexFintype : Fintype (T).Index :=
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

local instance finiteTerminalClosureWholeFintype : Fintype W.Index := W.finiteIndex

variable (r : {v // v ∈ R.parents.roots}) (side : Bool)

local notation "τ" => R.terminalTime level r
local notation "bank" => K.wholeTerminalBank compact nonempty R no_boundary W r side


/-- Construct supported Jordan closing links for an entire actual original terminal bank.
The intrinsic trace, radial geometry, linear support and outward link are all derived.
Every original fine vertex and cut-constraint line has controlled generic incidence. -/
theorem exists_compatibleMeshTerminalBank_supported_closure {d δ : ℝ}
    (behind : 0 < d) (room : 0 < δ) :
    ∃ n : ℕ, ∃ chain : ((T).pairedComplex.boundarySystem (Fcut).retain).Chain n,
      Set.range (K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side) = (T).pairedComplex.boundaryChainTrace chain ∧
      let P := ((T).pairedFolding.boundarySpatialChain chain).affineMap Cap.horizontal.toAffineMap
      ∃ (q c : Plane) (height : Plane →ₗ[ℝ] ℝ),
        dist q (R.exterior.point (R.terminalIndex r) -
          d • R.exterior.direction (R.exterior.slope (R.terminalIndex r))) < δ ∧
        P.RadialFrom q 0 ∧ 0 < dist q (P.vertex 0) ∧
        dist q (P.vertex 0) < dist q (P.vertex (Fin.last (n + 1))) ∧
        (∀ z ∈ Set.range P.path, 0 ≤ height (z - q)) ∧ height (c - q) < 0 ∧
        0 < inner ℝ (P.vertex (Fin.last (n + 1)) - q)
          (c - P.vertex (Fin.last (n + 1))) ∧
        (∀ i, K.compatibleCutEquations compact nonempty R no_boundary level higher i q ≠ 0 ∧
          K.compatibleCutEquations compact nonempty R no_boundary level higher i c ≠ 0) ∧
        (∀ v : (T).pairedComplex.Vertex Set.univ,
          q ≠ (Q).projectedVertex v ∧ c ≠ (Q).projectedVertex v) ∧
        (∀ v : (T).pairedComplex.Vertex Set.univ,
          (Q).projectedVertex v ∈ segment ℝ (P.vertex 0) q →
            (Q).projectedVertex v = P.vertex 0) ∧
        (∀ v : (T).pairedComplex.Vertex Set.univ,
          (Q).projectedVertex v ∉ segment ℝ q c) ∧
        (∀ v : (T).pairedComplex.Vertex Set.univ,
          (Q).projectedVertex v ∈ segment ℝ (P.vertex (Fin.last (n + 1))) c →
            (Q).projectedVertex v = P.vertex (Fin.last (n + 1))) ∧
        Schoenflies.IsJordanCurve (P.threeSegmentClosure q c) := by
  obtain ⟨n, chain, index, named, trace, source, finish⟩ :=
    K.exists_compatibleMeshTerminalBank_chain compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side
  have selected (i : Fin (n + 1)) : chain.point i ∈
      K.compatibleMeshTerminalBankEnds compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side := by
    rw [named]
    exact (index i).property
  obtain ⟨time, increasing, initial, terminal, matching⟩ :=
    K.parameterize_compatibleMeshTerminalBank_chain compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side chain selected source finish
  let P := ((T).pairedFolding.boundarySpatialChain chain).affineMap Cap.horizontal.toAffineMap
  let origin := R.exterior.point (R.terminalIndex r)
  let direction := R.exterior.direction (R.exterior.slope (R.terminalIndex r))
  have points (i : Fin (n + 1)) (u : unitInterval) :
      P.point i u = R.exterior.ray (R.terminalIndex r)
        (closedNonnegativeIntervalLineMap (time i.castSucc).val (time i.succ).val τ
          (time i.castSucc).property.1
          (increasing (show i.castSucc < i.succ from Fin.castSucc_lt_succ)).le
          (time i.succ).property.2 u).val := by
    have physical := ((T).pairedFolding.boundarySpatialChain_point chain i u).trans
      ((congrArg ((T).pairedFolding.toSpace (Fcut).retain) (matching i u)).trans
        (K.fold_compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r side _))
    exact (PolygonalChain.affineMap_point _ Cap.horizontal.toAffineMap i u).trans
      ((congrArg Cap.horizontal physical).trans (SpatialEnvelope.horizontal_point M.plane _))
  have position (j : Fin (n + 2)) : P.vertex j = origin + (time j).val • direction := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · have last := points (Fin.last n) 1
      rw [PolygonalChain.point_one, closedIntervalLineMap_one, Fin.succ_last] at last
      exact last
    · have first := points i 0
      rw [PolygonalChain.point_zero, closedIntervalLineMap_zero] at first
      exact first
  have nonzero : direction ≠ 0 := by
    intro zero
    have unit := R.exterior.unit (R.terminalIndex r)
    change ‖direction‖ = 1 at unit
    rw [zero, norm_zero] at unit
    exact zero_ne_one unit
  have ordered : StrictMono (fun j => (time j).val) :=
    fun i j before => increasing before
  obtain ⟨strict, first, last, frame, inside_frame⟩ :=
    P.ordered_ray_closure_geometry origin direction nonzero (fun j => (time j).val)
      (fun j => (time j).property.1) ordered position behind
  obtain ⟨q, c, height, close, radial, initial_distance, progress, supported_height, negative,
      outward, regular, avoids, initial_link, middle_link, final_link, jordan⟩ :=
    P.exists_supported_vertex_avoiding_wedge_closure (origin - d • direction) strict first last
      frame inside_frame (Q).projectedVertex
      (K.compatibleCutEquations compact nonempty R no_boundary level higher)
      (K.compatibleCutEquations_ne_zero compact nonempty R no_boundary level higher) room
  exact ⟨n, chain, trace, q, c, height, close, radial, initial_distance, progress, supported_height,
    negative, outward, regular, avoids, initial_link, middle_link, final_link, jordan⟩

/-- Entire original terminal banks admit supported generic closing links with the new
radial source arbitrarily close to their named original source vertex. -/
theorem exists_compatibleMeshTerminalBank_supported_closure_near_source {δ : ℝ}
    (room : 0 < δ) :
    ∃ n : ℕ, ∃ chain : ((T).pairedComplex.boundarySystem (Fcut).retain).Chain n,
      Set.range (K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side) = (T).pairedComplex.boundaryChainTrace chain ∧
      let P := ((T).pairedFolding.boundarySpatialChain chain).affineMap Cap.horizontal.toAffineMap
      ∃ (q c : Plane) (height : Plane →ₗ[ℝ] ℝ),
        dist q (K.projectedVertex r.val) < δ ∧
        P.RadialFrom q 0 ∧ 0 < dist q (P.vertex 0) ∧
        dist q (P.vertex 0) < dist q (P.vertex (Fin.last (n + 1))) ∧
        (∀ z ∈ Set.range P.path, 0 ≤ height (z - q)) ∧ height (c - q) < 0 ∧
        0 < inner ℝ (P.vertex (Fin.last (n + 1)) - q)
          (c - P.vertex (Fin.last (n + 1))) ∧
        (∀ i, K.compatibleCutEquations compact nonempty R no_boundary level higher i q ≠ 0 ∧
          K.compatibleCutEquations compact nonempty R no_boundary level higher i c ≠ 0) ∧
        (∀ v : (T).pairedComplex.Vertex Set.univ,
          q ≠ (Q).projectedVertex v ∧ c ≠ (Q).projectedVertex v) ∧
        (∀ v : (T).pairedComplex.Vertex Set.univ,
          (Q).projectedVertex v ∈ segment ℝ (P.vertex 0) q →
            (Q).projectedVertex v = P.vertex 0) ∧
        (∀ v : (T).pairedComplex.Vertex Set.univ,
          (Q).projectedVertex v ∉ segment ℝ q c) ∧
        (∀ v : (T).pairedComplex.Vertex Set.univ,
          (Q).projectedVertex v ∈ segment ℝ (P.vertex (Fin.last (n + 1))) c →
            (Q).projectedVertex v = P.vertex (Fin.last (n + 1))) ∧
        Schoenflies.IsJordanCurve (P.threeSegmentClosure q c) := by
  have half : 0 < δ / 2 := half_pos room
  obtain ⟨n, chain, trace, q, c, height, close, rest⟩ :=
    K.exists_compatibleMeshTerminalBank_supported_closure compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side (d := δ / 2) (δ := δ / 2) half half
  have origin : R.exterior.point (R.terminalIndex r) = K.projectedVertex r.val :=
    R.exterior_points _
  have shift_distance : dist
      (R.exterior.point (R.terminalIndex r) -
        (δ / 2) • R.exterior.direction (R.exterior.slope (R.terminalIndex r)))
      (K.projectedVertex r.val) = δ / 2 := by
    rw [← origin, dist_eq_norm', sub_sub_cancel, norm_smul, Real.norm_of_nonneg half.le,
      R.exterior.unit, mul_one]
  refine ⟨n, chain, trace, q, c, height, ?_, rest⟩
  have triangle := dist_triangle q
    (R.exterior.point (R.terminalIndex r) -
      (δ / 2) • R.exterior.direction (R.exterior.slope (R.terminalIndex r)))
    (K.projectedVertex r.val)
  rw [shift_distance] at triangle
  linarith

end Unfoldings.ConvexRoof
