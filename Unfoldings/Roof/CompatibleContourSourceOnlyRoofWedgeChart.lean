module

public import Unfoldings.Roof.CompatibleContourSourceOnlyRoofWedgeMarks
public import Unfoldings.Roof.CompatibleMeshCornerCharts
public import Unfoldings.Roof.CurvatureNonnegative
public import Unfoldings.Complex.StrictCopyAngles
public import Unfoldings.Complex.DirectedBoundaryPathReversal
public import Unfoldings.Complex.BoundaryBankLength
public import Unfoldings.Cone.DirectedIntervalChart

/-! Normalized whole charts for the original roof wedges between child excursions. -/

@[expose] public section

noncomputable section

open scoped ENNReal

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

local instance sourceOnlyRoofWedgeChartMarksFintype : Fintype (T).Index :=
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

local instance sourceOnlyRoofWedgeChartWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W
local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "Retain" => PotentialCutForest.retain Fcut
local notation "VertexAt[" w "]" => TriangleComplex.vertexPoint D Retain w
local notation "Forget[" w "]" => TriangleComplex.vertexForgetCuts D (Set.subset_univ Retain) w
local notation "Height[" x "]" => SlopeEnvelope.height (K.clippedExtension slopes compact nonempty)
  (Cap.horizontal (SpatialFolding.toSpace
    (SpatialEnvelope.Triangulation.pairedFolding
      (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) Retain x))
local notation "BankAt[" e "," side "]" => TriangleComplex.contourParentBank D Selection contour
  (PotentialCutForest.boundary_roots Fcut) starts (Subtype.val e) (Subtype.property e) side

local notation "Edge" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Turn" => TriangleComplex.boundaryTurn D Retain

private theorem roof_bank_speed_reverse (b : (D).BoundaryEnd Retain) :
    (D).boundaryBankLength (Turn b) = (D).boundaryBankLength b := by
  have bank : ((D).boundaryEndEquiv Retain (Turn b)).1 =
      ((D).boundaryEndEquiv Retain b).1 := ((D).boundaryEnd_bank_eq_iff Retain _ _).mpr (Or.inr rfl)
  have edge : (D).germEdge (Turn b).val = (D).germEdge b.val := congrArg Subtype.val bank
  rw [(D).boundaryBankLength_eq_edge, (D).boundaryBankLength_eq_edge, edge]

set_option maxHeartbeats 450000 in
-- The two dependent bank traces use the same whole-roof isometry at the rewritten center.
/-- The old return and new entrance banks point along the rays of the original
roof wedge, measured by the original arclength from parameter one. -/
theorem compatibleContourSourceOnlyRoofWedge_sector_chart
    (old_child new_child : Edge) (j : Fin (contour.length + 1))
    (after_old : finRotate (contour.length + 1) ((D).contourParentInterval Selection contour
      (Fcut).boundary_roots starts old_child.val old_child.property).leave = j)
    (before_new : ((D).contourParentInterval Selection contour (Fcut).boundary_roots starts
      new_child.val new_child.property).enter = j)
    (nonroot : (D).contourOriginalVertex Selection contour j ∉ (Fcut).parents.roots) :
    let w := (D).boundaryEndVertex Retain (contour.cycle.point j)
    let θ := (D).totalAngle Retain w
    let x := Map VertexAt[w]
    θ < 2 * Real.pi ∧
    ∃ r : ℝ, 0 < r ∧
      ∃ chart : Metric.eball x (ENNReal.ofReal r) ≃ᵢ
          Metric.eball (closedAngularSectorOrigin ((D).totalAngle_pos Retain w).le)
            (ENNReal.ofReal r),
        (∀ (t : unitInterval) (near : edist (Base (.inl old_child) false t) x < ENNReal.ofReal r),
          (chart ⟨Base (.inl old_child) false t, near⟩).val.val =
            ((1 - t.val) * (D).boundaryBankLength BankAt[old_child,false] : ℝ)) ∧
        (∀ (t : unitInterval) (near : edist (Base (.inl new_child) true t) x < ENNReal.ofReal r),
          (chart ⟨Base (.inl new_child) true t, near⟩).val.val =
            ((1 - t.val) * (D).boundaryBankLength BankAt[new_child,true]) • polarRay θ) := by
  let p := Turn BankAt[old_child,false]
  let q := Turn BankAt[new_child,true]
  let w := (D).boundaryEndVertex Retain (contour.cycle.point j)
  let v := Forget[w]
  have below := K.compatibleContourRoofVertex_height_lt_of_nonroot compact nonempty R no_boundary
    level higher M positive inner_disk beta acute w nonroot
  have germs := (D).contour_parent_wedge_end_eq_iff Selection contour (Fcut).boundary_roots
    starts old_child new_child j after_old before_new
  have hp : (D).boundaryEndVertex Retain p = w := (germs p).mpr (Or.inl rfl)
  have hq : (D).boundaryEndVertex Retain q = w := (germs q).mpr (Or.inr rfl)
  have diff : q ≠ p := by
    intro h
    have same : (new_child, true) = (old_child, false) :=
      (D).contourParentBank_injective Selection contour (Fcut).boundary_roots starts
        (((D).boundaryTurn_involutive Retain).injective h)
    exact Bool.noConfusion (congrArg Prod.snd same)
  have mate : (D).boundaryMate Retain p = q :=
    ((D).exists_unique_other_boundaryEnd Retain p).unique ((D).boundaryMate_spec Retain p)
      ⟨diff, hq.trans hp.symm⟩
  let A := (D).contourParentInterval Selection contour (Fcut).boundary_roots starts
    old_child.val old_child.property
  let z := (D).boundaryEndVertex Retain (contour.cycle.point A.enter)
  have at_parent : v = (Fcut).parents.parent old_child.val :=
    (congrArg ((D).contourOriginalVertex Selection contour) after_old).symm.trans
      ((congrArg (fun x : (D).Vertex Retain => Forget[x])
        ((D).contourParentBank_finish_copies Selection contour (Fcut).boundary_roots starts
          old_child.val old_child.property).2).symm.trans
            ((D).contourParentBank_finish Selection contour (Fcut).boundary_roots starts
              old_child.val old_child.property false))
  obtain ⟨advance, start_parent, _, _⟩ := (D).contourChild_consecutive_parent_visits Selection
    contour (Fcut).boundary_roots starts old_child.val old_child.property
    (at_parent ▸ nonroot)
  have other : z ≠ w := by
    intro same
    have eq := (D).boundaryCycle_vertices_injective Retain contour.cycle contour.closes same
    have rank := congrArg Fin.val (eq.trans after_old.symm)
    change A.enter.val = (finRotate (contour.length + 1) A.leave).val at rank
    change (finRotate (contour.length + 1) A.leave).val = A.leave.val + 1 at advance
    have before := A.ordered
    omega
  have original : Forget[z] = Forget[w] := start_parent.trans at_parent.symm
  have internal : ¬ (D).IsBoundaryVertex Set.univ v :=
    fun b => nonroot ((Fcut).boundary_roots b)
  let cap := (T).toTriangulation.normalizedCap
    (K.compatibleCutMesh_conforming compact nonempty R no_boundary level higher M positive inner_disk)
    (K.compatible_section_interior compact nonempty R level higher M)
  have small : (D).totalAngle Retain w < 2 * Real.pi :=
    ((D).totalAngle_lt_forgetCuts_of_other_copy (Set.subset_univ Retain) w z other.symm original).trans_le
      (cap.totalAngle_le_two_pi v internal)
  have speeds (b : (D).BoundaryEnd Retain) (at_vertex : (D).boundaryEndVertex Retain b = w)
      (t : unitInterval) :
      ENNReal.ofReal (t.val * (D).boundaryBankLength b) =
        edist (Map ((D).directedBoundaryPath b t)) (Map VertexAt[w]) := by
    have zero : (D).directedBoundaryPath b 0 = VertexAt[w] :=
      ((D).directedBoundaryPath_zero b).trans (congrArg ((D).vertexPoint Retain) at_vertex)
    calc
      _ = ENNReal.ofReal ((D).boundaryBankLength b) * edist t (0 : unitInterval) := by
        rw [mul_comm t.val, ENNReal.ofReal_mul ((D).boundaryBankLength_pos b).le, edist_dist]
        congr 1
        apply congrArg ENNReal.ofReal
        change t.val = dist t.val 0
        rw [Real.dist_eq, sub_zero, abs_of_nonneg t.property.1]
      _ = _ :=
        (((T).pairedFolding.edist_directedBoundaryPath_eq_length b t 0).symm.trans
          (K.compatibleWholeMap_edist_bank compact nonempty R no_boundary level higher M
            positive inner_disk beta acute W b t 0).symm).trans
          (congrArg (fun y => edist (Map ((D).directedBoundaryPath b t)) (Map y)) zero)
  have chart_data := (D).exists_directedIntervalChart Retain p Map
    (hp.symm ▸ small) (hp.symm ▸ speeds)
    (K.compatibleMesh_corner_fan_chart compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W _ (hp.symm ▸ below))
  rw [mate, hp] at chart_data
  obtain ⟨r, rpos, chart, first, last⟩ := chart_data
  refine ⟨small, r, rpos, chart, ?_, ?_⟩
  · intro t near
    have eq : Map ((D).directedBoundaryPath p (unitInterval.symm t)) =
        Base (.inl old_child) false t := by
      change Map ((D).directedBoundaryPath (Turn BankAt[old_child,false]) (unitInterval.symm t)) =
        Map ((D).directedBoundaryPath BankAt[old_child,false] t)
      exact congrArg Map (((D).directedBoundaryPath_turn BankAt[old_child,false]
        (unitInterval.symm t)).trans (congrArg ((D).directedBoundaryPath BankAt[old_child,false])
          (unitInterval.symm_symm t)))
    have close : edist (Map ((D).directedBoundaryPath p (unitInterval.symm t)))
        (Map VertexAt[w]) < ENNReal.ofReal r :=
      (congrArg (fun y : W.Cut => edist y (Map VertexAt[w])) eq).trans_lt near
    have h := first (unitInterval.symm t) close
    change (chart ⟨_, _⟩).val.val =
      ((unitInterval.symm t).val * (D).boundaryBankLength (Turn BankAt[old_child,false]) : ℝ) at h
    have speed : (D).boundaryBankLength p = (D).boundaryBankLength BankAt[old_child,false] :=
      roof_bank_speed_reverse K compact nonempty R no_boundary level higher M positive inner_disk
        beta acute BankAt[old_child,false]
    rw [speed, unitInterval.coe_symm_eq] at h
    have same : (⟨Map ((D).directedBoundaryPath p (unitInterval.symm t)), close⟩ :
        Metric.eball (Map VertexAt[w]) (ENNReal.ofReal r)) = ⟨_, near⟩ := Subtype.ext eq
    exact (congrArg (fun z => (chart z).val.val) same).symm.trans h
  · intro t near
    have eq : Map ((D).directedBoundaryPath q (unitInterval.symm t)) =
        Base (.inl new_child) true t := by
      change Map ((D).directedBoundaryPath (Turn BankAt[new_child,true]) (unitInterval.symm t)) =
        Map ((D).directedBoundaryPath BankAt[new_child,true] t)
      exact congrArg Map (((D).directedBoundaryPath_turn BankAt[new_child,true]
        (unitInterval.symm t)).trans (congrArg ((D).directedBoundaryPath BankAt[new_child,true])
          (unitInterval.symm_symm t)))
    have close : edist (Map ((D).directedBoundaryPath q (unitInterval.symm t)))
        (Map VertexAt[w]) < ENNReal.ofReal r :=
      (congrArg (fun y : W.Cut => edist y (Map VertexAt[w])) eq).trans_lt near
    have h := last (unitInterval.symm t) close
    change (chart ⟨_, _⟩).val.val =
      ((unitInterval.symm t).val * (D).boundaryBankLength (Turn BankAt[new_child,true])) •
        polarRay ((D).totalAngle Retain w) at h
    have speed : (D).boundaryBankLength q = (D).boundaryBankLength BankAt[new_child,true] :=
      roof_bank_speed_reverse K compact nonempty R no_boundary level higher M positive inner_disk
        beta acute BankAt[new_child,true]
    rw [speed, unitInterval.coe_symm_eq] at h
    have same : (⟨Map ((D).directedBoundaryPath q (unitInterval.symm t)), close⟩ :
        Metric.eball (Map VertexAt[w]) (ENNReal.ofReal r)) = ⟨_, near⟩ := Subtype.ext eq
    exact (congrArg (fun z => (chart z).val.val) same).symm.trans h

end Unfoldings.ConvexRoof
