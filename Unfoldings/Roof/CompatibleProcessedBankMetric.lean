module

public import Unfoldings.Roof.CompatibleProcessedMeshCharts
public import Unfoldings.Polyhedron.CutEdgeFibers
public import Unfoldings.Polyhedron.DirectedBankMetric
public import Unfoldings.Metric.DilationNonexpandingTransport
public import Unfoldings.Roof.CompatiblePartialWindowPairedFiber
public import Unfoldings.Topology.TwoClosedLifts

/-! Whole original finite banks and their two metric copies in intermediate forest cuts. -/

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

local instance processedBankMetricIndexFintype : Fintype (T).Index :=
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
variable (W : R.WholeCutModel M)

local instance processedBankMetricWholeFintype : Fintype W.Index := W.finiteIndex

local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S
local notation "CutsAt[" S "]" => K.compatibleMeshProcessedCarrier compact nonempty R no_boundary
  level higher M positive inner_disk beta acute S
local notation "ClosedAt[" S "]" => K.isClosed_compatibleMeshProcessedCarrier compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "IncludedAt[" S "]" => K.compatibleMeshProcessedCarrier_subset compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "OutsideAt[" S "]" =>
  fun f => Disjoint.mono_right IncludedAt[S]
    (K.compatibleMesh_cut_disjoint_interior compact nonempty R no_boundary level higher M positive
      inner_disk f)
local notation "RemovedAt[" S "]" => K.compatibleMeshProcessed_removed_edge compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "KeptAt[" S "]" => K.compatibleMeshProcessed_retained_open_edge compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S

local notation "MapAt[" S "]" => K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute W S

/-- Every entire original finite bank retains its exact distances after inclusion in
the intermediate whole cut, even at its two original endpoint copies. -/
def compatibleMeshProcessedBankDilation (S : (Fcut).parents.ParentFrontier)
    (p : (T).pairedComplex.BoundaryEnd RetainAt[S]) :
    unitInterval →ᵈ W.partition.Cut CutsAt[S] :=
  dilationOfNonexpandingTransport ((T).pairedFolding.directedBankDilation p) MapAt[S]
    (K.compatibleMeshProcessedWholeMap_lipschitz compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S)
    (fun x => (W.partition.restoreCut CutsAt[S] x).val)
    (by
      intro x y
      have bound := (PolygonalPoint.ambient_lipschitz.comp
        (W.partition.restoreCut_lipschitz CutsAt[S])) x y
      simpa only [Function.comp_apply, ENNReal.coe_one, one_mul, edist_dist] using bound)
    (fun u => (T).pairedFolding.toSpace RetainAt[S]
      ((T).pairedComplex.directedBoundaryPath p u))
    (fun s t => ((T).pairedFolding.edist_directedBoundaryPath_eq_spatial p s t).symm)
    (fun u => K.restore_compatibleMeshProcessedWholeMap compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S ((T).pairedComplex.directedBoundaryPath p u))

@[simp] theorem compatibleMeshProcessedBankDilation_apply (S : (Fcut).parents.ParentFrontier)
    (p : (T).pairedComplex.BoundaryEnd RetainAt[S]) (u : unitInterval) :
    K.compatibleMeshProcessedBankDilation compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W S p u = MapAt[S] ((T).pairedComplex.directedBoundaryPath p u) := by
  calc
    _ = MapAt[S] ((T).pairedFolding.directedBankDilation p u) :=
      dilationOfNonexpandingTransport_apply _ _ _ _ _ _ _ _ u
    _ = _ := congrArg MapAt[S] ((T).pairedFolding.directedBankDilation_apply p u)

/-- The original entire bank remains closed and embedded in the actual whole intermediate cut. -/
theorem compatibleMeshProcessedBank_isClosedEmbedding (S : (Fcut).parents.ParentFrontier)
    (p : (T).pairedComplex.BoundaryEnd RetainAt[S]) :
    Topology.IsClosedEmbedding (fun u : unitInterval =>
      MapAt[S] ((T).pairedComplex.directedBoundaryPath p u)) :=
  Dilation.isClosedEmbedding (K.compatibleMeshProcessedBankDilation compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W S p)

/-- Every whole-cut copy strictly below the old level over a removed edge's nonvertex
point is the image of one of that edge's two original finite banks. -/
theorem compatibleMeshProcessedWholeMap_bank_copies_exhaust
    (S : (Fcut).parents.ParentFrontier) (s : (T).pairedComplex.Seam)
    (removed : s ∉ RetainAt[S])
    (q : ((T).pairedComplex.triangle ((T).pairedComplex.left s).face).Edge
      ((T).pairedComplex.left s).edge)
    (regular : ¬ ((T).pairedComplex.triangle ((T).pairedComplex.left s).face).IsVertex q.val)
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.place ((T).pairedComplex.left s).face q.val)) < level)
    (x : W.partition.Cut CutsAt[S])
    (position : (W.partition.restoreCut CutsAt[S] x).val =
      (T).pairedFolding.place ((T).pairedComplex.left s).face q.val) :
    x = MapAt[S] ((T).pairedComplex.bankMap RetainAt[S]
        ((T).pairedComplex.leftBank RetainAt[S] s removed) q) ∨
      x = MapAt[S] ((T).pairedComplex.bankMap RetainAt[S]
        ((T).pairedComplex.rightBank RetainAt[S] s removed) ((T).pairedComplex.identify s q)) := by
  have interior_point : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut CutsAt[S] x).val) < level := by
    rwa [position]
  obtain ⟨y, at_x, _⟩ := K.exists_compatibleMeshProcessed_ball_chart compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W S x interior_point
  have physical : (T).pairedFolding.toSpace RetainAt[S] y =
      (T).pairedFolding.place ((T).pairedComplex.left s).face q.val :=
    (K.restore_compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S y).symm.trans
      ((congrArg (fun z => (W.partition.restoreCut CutsAt[S] z).val) at_x).trans position)
  rcases (Q).folding.eq_leftBank_or_rightBank_of_regular_position (Q).embedded RetainAt[S]
      s removed q regular y physical with first | last
  · exact Or.inl (at_x.symm.trans (congrArg MapAt[S] first))
  · exact Or.inr (at_x.symm.trans (congrArg MapAt[S] last))

/-- A strict-interior original mesh copy is the unique finite copy of its whole-cut image. -/
theorem compatibleMeshProcessedWholeMap_injective_at (S : (Fcut).parents.ParentFrontier)
    (x : (T).pairedComplex.Realization RetainAt[S])
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.toSpace RetainAt[S] x)) < level)
    (y : (T).pairedComplex.Realization RetainAt[S]) (same : MapAt[S] x = MapAt[S] y) : x = y :=
  (V).partialPairedMeshMap_injective_at proper full (T).toTriangulation domain heights CutsAt[S]
    ClosedAt[S] IncludedAt[S] OutsideAt[S] W conforming RetainAt[S] RemovedAt[S] KeptAt[S] x
    (by apply SpatialEnvelope.levelEquation_positive; rw [M.height_eq]; linarith) y same

/-- One whole named original seam bank, parameterized on the same left edge on both sides. -/
@[macro_inline] def compatibleMeshProcessedSeamBank (S : (Fcut).parents.ParentFrontier)
    (s : (T).pairedComplex.Seam) (removed : s ∉ RetainAt[S]) (side : Bool)
    (q : ((T).pairedComplex.triangle ((T).pairedComplex.left s).face).Edge
      ((T).pairedComplex.left s).edge) : W.partition.Cut CutsAt[S] :=
  if side then MapAt[S] ((T).pairedComplex.bankMap RetainAt[S]
    ((T).pairedComplex.rightBank RetainAt[S] s removed) ((T).pairedComplex.identify s q))
  else MapAt[S] ((T).pairedComplex.bankMap RetainAt[S]
    ((T).pairedComplex.leftBank RetainAt[S] s removed) q)

local notation "SeamBankAt[" S "," s "," h "," b "]" =>
  K.compatibleMeshProcessedSeamBank compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W S s h b

/-- Opposite finite whole-bank copies remain distinct at every nonvertex old interior point. -/
theorem compatibleMeshProcessedSeamBank_ne (S : (Fcut).parents.ParentFrontier)
    (s : (T).pairedComplex.Seam) (removed : s ∉ RetainAt[S]) (side other : Bool)
    (different : side ≠ other)
    (q t : ((T).pairedComplex.triangle ((T).pairedComplex.left s).face).Edge
      ((T).pairedComplex.left s).edge)
    (regular : ¬ ((T).pairedComplex.triangle ((T).pairedComplex.left s).face).IsVertex q.val)
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.place ((T).pairedComplex.left s).face q.val)) < level) :
    SeamBankAt[S,s,removed,side] q ≠ SeamBankAt[S,s,removed,other] t := by
  have regular_right : ¬ (T).pairedComplex.IsVertex
      ((T).pairedComplex.edgePoint ((T).pairedComplex.right s)
        ((T).pairedComplex.identify s q)) := by
    intro vertex
    exact regular (((T).pairedComplex.glue_preserves_vertex Set.univ _ _
      ⟨s, Set.mem_univ _, q, rfl, rfl⟩).mpr vertex)
  have below_left : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.toSpace RetainAt[S]
        ((T).pairedComplex.bankMap RetainAt[S]
          ((T).pairedComplex.leftBank RetainAt[S] s removed) q))) < level := by
    have folded := (T).pairedFolding.toSpace_bankMap
      ((T).pairedComplex.leftBank RetainAt[S] s removed) q
    exact (congrArg (fun z : Space =>
      (K.clippedExtension slopes compact nonempty).height (Cap.horizontal z)) folded).trans_lt below
  cases side <;> cases other
  · exact (different rfl).elim
  · intro same
    apply (T).pairedComplex.bankMap_ne_of_ne RetainAt[S]
      ((T).pairedComplex.leftBank_ne_rightBank RetainAt[S] s removed) q
      ((T).pairedComplex.identify s t) regular
    exact K.compatibleMeshProcessedWholeMap_injective_at compact nonempty R no_boundary level higher
      M positive inner_disk beta acute W S _ below_left _ same
  · intro same
    apply (T).pairedComplex.bankMap_ne_of_ne RetainAt[S]
      ((T).pairedComplex.leftBank_ne_rightBank RetainAt[S] s removed).symm
      ((T).pairedComplex.identify s q) t regular_right
    apply K.compatibleMeshProcessedWholeMap_injective_at compact nonempty R no_boundary level higher
      M positive inner_disk beta acute W S _ _ _ same
    have folded := ((T).pairedFolding.toSpace_bankMap
      ((T).pairedComplex.rightBank RetainAt[S] s removed) ((T).pairedComplex.identify s q)).trans
      ((T).pairedFolding.joined s q).symm
    exact (congrArg (fun z : Space =>
      (K.clippedExtension slopes compact nonempty).height (Cap.horizontal z)) folded).trans_lt below
  · exact (different rfl).elim

/-- Each named whole original seam-bank copy depends continuously on the original edge point. -/
theorem continuous_compatibleMeshProcessedSeamBank (S : (Fcut).parents.ParentFrontier)
    (s : (T).pairedComplex.Seam) (removed : s ∉ RetainAt[S]) (side : Bool) :
    Continuous SeamBankAt[S,s,removed,side] := by
  have bounded := K.compatibleMeshProcessedWholeMap_lipschitz compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W S
  cases side
  · exact bounded.continuous.comp ((T).pairedComplex.bankMap_lipschitz RetainAt[S]
      ((T).pairedComplex.leftBank RetainAt[S] s removed)).continuous
  · exact bounded.continuous.comp (((T).pairedComplex.bankMap_lipschitz RetainAt[S]
      ((T).pairedComplex.rightBank RetainAt[S] s removed)).continuous.comp
        ((T).pairedComplex.identify s).continuous)

/-- A connected whole-cut curve over one original edge interior follows one fixed actual
bank. It cannot change sides at new subdivision vertices. -/
theorem compatibleMeshProcessedSeamBank_side_constant
    {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    (S : (Fcut).parents.ParentFrontier) (s : (T).pairedComplex.Seam) (removed : s ∉ RetainAt[S])
    (curve : A → W.partition.Cut CutsAt[S]) (continuous_curve : Continuous curve)
    (point : A → ((T).pairedComplex.triangle ((T).pairedComplex.left s).face).Edge
      ((T).pairedComplex.left s).edge)
    (regular : ∀ a, ¬ ((T).pairedComplex.triangle ((T).pairedComplex.left s).face).IsVertex
      (point a).val)
    (below : ∀ a, (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.place ((T).pairedComplex.left s).face
        (point a).val)) < level)
    (position : ∀ a, (W.partition.restoreCut CutsAt[S] (curve a)).val =
      (T).pairedFolding.place ((T).pairedComplex.left s).face (point a).val) :
    ∃ side : Bool, ∀ a, curve a = SeamBankAt[S,s,removed,side] (point a) := by
  apply exists_fixed_bool_lift curve continuous_curve (fun side => SeamBankAt[S,s,removed,side])
    (fun side => (isCompact_range
      (K.continuous_compatibleMeshProcessedSeamBank compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W S s removed side)).isClosed) point
  · intro a
    rcases K.compatibleMeshProcessedWholeMap_bank_copies_exhaust compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S s removed (point a) (regular a) (below a)
      (curve a) (position a) with first | last
    · exact ⟨false, first⟩
    · exact ⟨true, last⟩
  · intro a side other different q
    exact K.compatibleMeshProcessedSeamBank_ne compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S s removed side other different (point a) q
      (regular a) (below a)

/-- Matching on a connected dense interior portion fixes every original endpoint copy too.
Only the physical original edge trace is supplied; the intrinsic bank side is derived. -/
theorem compatibleMeshProcessedSeamBank_side_of_dense_regular
    {A : Type*} [TopologicalSpace A]
    (S : (Fcut).parents.ParentFrontier) (s : (T).pairedComplex.Seam) (removed : s ∉ RetainAt[S])
    (curve : A → W.partition.Cut CutsAt[S]) (continuous_curve : Continuous curve)
    (point : A → ((T).pairedComplex.triangle ((T).pairedComplex.left s).face).Edge
      ((T).pairedComplex.left s).edge) (continuous_point : Continuous point)
    (portion : Set A) (connected : IsPreconnected portion) (dense : Dense portion)
    (regular : ∀ a ∈ portion,
      ¬ ((T).pairedComplex.triangle ((T).pairedComplex.left s).face).IsVertex (point a).val)
    (below : ∀ a ∈ portion, (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.place ((T).pairedComplex.left s).face
        (point a).val)) < level)
    (position : ∀ a, (W.partition.restoreCut CutsAt[S] (curve a)).val =
      (T).pairedFolding.place ((T).pairedComplex.left s).face (point a).val) :
    ∃ side : Bool, ∀ a, curve a = SeamBankAt[S,s,removed,side] (point a) := by
  let : PreconnectedSpace portion := Subtype.preconnectedSpace connected
  obtain ⟨side, same⟩ := K.compatibleMeshProcessedSeamBank_side_constant compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W S s removed
    (fun a : portion => curve a.val) (continuous_curve.comp continuous_subtype_val)
    (fun a : portion => point a.val) (fun a => regular a.val a.property)
    (fun a => below a.val a.property) (fun a => position a.val)
  have agrees : Set.EqOn curve (fun a => SeamBankAt[S,s,removed,side] (point a)) portion :=
    fun a member => same ⟨a, member⟩
  exact ⟨side, fun a => agrees.closure continuous_curve
    ((K.continuous_compatibleMeshProcessedSeamBank compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S s removed side).comp continuous_point) (dense a)⟩

end Unfoldings.ConvexRoof
