module

public import Unfoldings.Roof.CompatibleContourTerminalEdgeLabels
public import Unfoldings.Roof.CompatibleContourBankEmbeddings

/-! The last finite edge and its sides label the two actual whole roof tails. -/

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

local instance contourTerminalSideLabelMeshFintype : Fintype (T).Index :=
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

local instance contourTerminalSideLabelWholeFintype : Fintype W.Index := W.finiteIndex

local notation "ParentAt[" vertex "," nonroot "," side "," time "]" =>
  K.compatibleContourParentMark compact nonempty R no_boundary level higher M positive inner_disk
    beta acute contour starts W vertex nonroot side time

local notation "RootAt[" e "]" => K.compatibleMeshTerminalRoot compact nonempty R no_boundary
  level higher M positive inner_disk beta acute (Subtype.val e)
  (TriangleComplex.contourTerminalEdge_positive D Selection e)
local notation "SpeedAt[" e "]" => K.compatibleContourTerminalSpeed compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W e
local notation "Edge" => TriangleComplex.ContourTerminalEdge D Selection


/-- The last two original finite bank copies reach distinct whole-roof points.
A connected positive-time portion of each finite bank keeps one terminal side. -/
theorem compatibleContourTerminalEndpoint_ne (edge : Edge) :
    ParentAt[edge.val,edge.property.1,false,1] ≠ ParentAt[edge.val,edge.property.1,true,1] := by
  let root := RootAt[edge]
  let τ := R.terminalTime level root
  let d := (SpeedAt[edge]).val
  have τpos : 0 < τ := R.terminalTime_pos level higher root
  have dpos : 0 < d := K.compatibleContourTerminalSpeed_positive compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W edge
  let a := max 0 (1 - τ / (2 * d))
  have nonnegative : 0 ≤ a := le_max_left _ _
  have before : a < 1 := max_lt (by norm_num) (sub_lt_self _ (div_pos τpos (by positivity)))
  let A := Set.Icc a (1 : ℝ)
  let : ConnectedSpace A := Subtype.connectedSpace
    ⟨Set.nonempty_Icc.mpr before.le, isPreconnected_Icc⟩
  let unit (x : A) : unitInterval := ⟨x.val, nonnegative.trans x.property.1, x.property.2⟩
  have progress (x : A) : 0 < τ - (1 - x.val) * d := by
    have near : 1 - τ / (2 * d) ≤ x.val := (le_max_right _ _).trans x.property.1
    have size : (1 - x.val) * (2 * d) ≤ τ :=
      (le_div_iff₀ (by positivity : 0 < 2 * d)).mp (by linarith)
    linarith
  let time (x : A) : ℝ≥0 := ⟨_, (progress x).le⟩
  let mark (side : Bool) (x : A) := ParentAt[edge.val,edge.property.1,side,unit x]
  have stays (side : Bool) : ∃ bank, ∀ x : A, mark side x =
      K.wholeTerminalBank compact nonempty R no_boundary W root bank (time x) := by
    refine K.wholeTerminalBank_side_constant compact nonempty R no_boundary W root (mark side)
      ?_ time progress ?_
    · exact (Dilation.lipschitzWith (K.compatibleContourParentDilation compact nonempty R
        no_boundary level higher M positive inner_disk beta acute contour starts W edge.val
        edge.property.1 side)).continuous.comp (continuous_subtype_val.subtype_mk _)
    · intro x
      exact K.compatibleContourTerminalParentMark_horizontal compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts W edge side (unit x)
  obtain ⟨left, hl⟩ := stays false
  obtain ⟨right, hr⟩ := stays true
  let one : A := ⟨1, before.le, le_rfl⟩
  intro equal
  have same : left = right := by
    by_contra different
    exact K.wholeTerminalBank_ne compact nonempty R no_boundary W root left right different
      (time one) (time one) (progress one) ((hl one).symm.trans (equal.trans (hr one)))
  let x : A := ⟨(a + 1) / 2, by linarith, by linarith⟩
  have bounds : 0 < unit x ∧ unit x < 1 := by
    change 0 < (a + 1) / 2 ∧ (a + 1) / 2 < 1
    constructor <;> linarith
  have h : mark false x = mark true x := (hl x).trans (same ▸ (hr x).symm)
  let child : {v : (D).Vertex Set.univ // v ∉ (Fcut).parents.roots} :=
    ⟨edge.val, edge.property.1⟩
  have labels := K.compatibleContourParentMark_eq_interior compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W child child true false (unit x)
      (unit x) bounds h
  cases congrArg (fun p => p.2.1) labels

local notation "TailAt[" e "," side "," t "]" => K.compatibleContourTerminalMark compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts W e side t
local notation "TimeAt[" e "]" => NNReal.mk (R.terminalTime level RootAt[e])
  (LT.lt.le (CompatiblePotentialRouting.terminalTime_pos R level higher RootAt[e]))

/-- The actual whole roof tail follows a single original bank and its original affine time. -/
theorem compatibleContourTerminalMark_wholeBank (edge : Edge) (side : Bool) :
    ∃ label, ∀ t : ℝ≥0, TailAt[edge,side,t] =
      K.wholeTerminalBank compact nonempty R no_boundary W RootAt[edge] label
        (forwardBankParameter TimeAt[edge] SpeedAt[edge] t) := by
  unfold compatibleContourTerminalMark wholeTerminalContinuation
  exact ⟨_, fun _ => rfl⟩

/-- Equality of two whole roof tail marks recovers their exact edge, side, and parameter. -/
theorem compatibleContourTerminalMark_eq (edge other : Edge) (side other_side : Bool)
    (t s : ℝ≥0) (equal : TailAt[other,other_side,s] = TailAt[edge,side,t]) :
    (other, other_side, s) = (edge, side, t) := by
  let time (b : Edge) (u : ℝ≥0) := forwardBankParameter TimeAt[b] SpeedAt[b] u
  have time_pos (b : Edge) (u : ℝ≥0) : 0 < (time b u).val :=
    (R.terminalTime_pos level higher RootAt[b]).trans_le
      (le_add_of_nonneg_right (mul_nonneg (SpeedAt[b]).property u.property))
  have position (b : Edge) (flag : Bool) (u : ℝ≥0) :
      Cap.horizontal (W.partition.restoreCut R.carrier TailAt[b,flag,u]).val =
        R.exterior.ray (R.terminalIndex RootAt[b]) (time b u).val :=
    (congrArg Cap.horizontal (K.restore_compatibleContourTerminalMark compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W b flag u)).trans
        (SpatialEnvelope.horizontal_point _ _)
  have same_ray := (position other other_side s).symm.trans
    ((congrArg (fun x => Cap.horizontal (W.partition.restoreCut R.carrier x).val) equal).trans
      (position edge side t))
  have roots : RootAt[other] = RootAt[edge] := by
    by_contra h
    have different : (RootAt[other]).val ≠ (RootAt[edge]).val := fun h' => h (Subtype.ext h')
    exact Set.disjoint_left.mp
      (K.compatible_openPieces_pairwise_disjoint compact nonempty R no_boundary different)
      (R.terminal_ray_mem_openPiece RootAt[other] (time_pos other s))
      (same_ray.symm ▸ R.terminal_ray_mem_openPiece RootAt[edge] (time_pos edge t))
  have edge_eq := K.compatibleContourTerminalRoot_injective compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W roots
  subst other
  obtain ⟨left, hl⟩ := K.compatibleContourTerminalMark_wholeBank compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W edge other_side
  obtain ⟨right, hr⟩ := K.compatibleContourTerminalMark_wholeBank compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W edge side
  have labels : left = right := by
    by_contra different
    exact K.wholeTerminalBank_ne compact nonempty R no_boundary W RootAt[edge] left right different
      (time edge s) (time edge t) (time_pos edge s) ((hl s).symm.trans (equal.trans (hr t)))
  have endpoint : TailAt[edge,other_side,0] = TailAt[edge,side,0] :=
    (hl 0).trans (labels ▸ (hr 0).symm)
  have sides : other_side = side := by
    rw [K.compatibleContourTerminalMark_zero, K.compatibleContourTerminalMark_zero] at endpoint
    cases side <;> cases other_side
    · rfl
    · exact (K.compatibleContourTerminalEndpoint_ne compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W edge endpoint.symm).elim
    · exact (K.compatibleContourTerminalEndpoint_ne compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W edge endpoint).elim
    · rfl
  subst other_side
  have parameter := Dilation.injective (K.compatibleContourTailDilation compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W edge side) equal
  subst s
  rfl

end Unfoldings.ConvexRoof
