module

public import Unfoldings.FewestNets.ThreeExitRoofVertexMarks
public import Unfoldings.Cone.MarkedSectorGerm
public import Unfoldings.Complex.StrictCopyAngles
public import Unfoldings.Roof.CurvatureNonnegative

/-! Normalized angular-sector charts along the original roof banks. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

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

local notation "T[" h "]" => R.fineMesh level M h
local notation "D[" h "]" => SpatialEnvelope.FloorMesh.pairedComplex T[h]
local notation "F[" h "]" => R.fineMeshForest level M h
local notation "Sel[" h "]" => PotentialCutForest.selection F[h]

local instance calibratedRoofIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
    Fintype (T[h]).Index := @Fintype.ofFinite _ (T[h]).finite

variable (S : SourceContour (R := R) (M := M) (level := level))

local notation "T" => T[S.higher]
local notation "D" => D[S.higher]
local notation "Fcut" => F[S.higher]
local notation "Selection" => Sel[S.higher]
local notation "Base" => contourBaseMark L S
local notation "Attachment" => PotentialCutForest.ContourAttachment Fcut
local notation "Param" => PotentialCutForest.contourAttachmentParameter Fcut

local notation "restore" => SpatialEnvelope.WholePartition.restoreCut L.whole.partition R.wholeCarrier
local notation "retain" => PotentialCutForest.retain Fcut
local notation "intoCut" => L.fineMeshWholeMap S.higher
local notation "Q" => SpatialEnvelope.FloorMesh.roof T
  (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M S.higher)
local notation "Forget[" w "]" => TriangleComplex.vertexForgetCuts D (Set.subset_univ retain) w
local notation "CutPoint[" w "]" => intoCut (TriangleComplex.vertexPoint D retain w)

local notation "Child" => {v : TriangleComplex.Vertex D Set.univ // v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Exit" => TriangleComplex.ContourTerminalEdge D Selection
local notation "Germ[" e "," side "]" => TriangleComplex.contourParentBank D Selection S.contour
  (PotentialCutForest.boundary_roots Fcut) S.starts (Subtype.val e) (Subtype.property e) side

local notation "Outward" => contourFiniteRoofGerm S
local notation "BankLength[" e "]" => TriangleComplex.boundaryBankLength D Germ[e,false]

private theorem contourRoof_endpoint_length (e : Child) (side finish : Bool) :
    (D).boundaryBankLength (Outward e side finish) = BankLength[e] := by
  have side_eq : (D).boundaryBankLength Germ[e,side] = BankLength[e] := by
    let folding := (T).pairedFolding
    have left := folding.boundaryBankLength_eq_germDirection_norm Germ[e,side]
    have right := folding.boundaryBankLength_eq_germDirection_norm Germ[e,false]
    have first := folding.contourParentBank_direction Selection S.contour (Fcut).boundary_roots
      S.starts e.val e.property side
    have second := folding.contourParentBank_direction Selection S.contour (Fcut).boundary_roots
      S.starts e.val e.property false
    exact left.trans ((congrArg norm (first.trans second.symm)).trans right.symm)
  cases finish
  · exact side_eq
  · have tag : (D).germEdge ((D).boundaryTurn retain Germ[e,side]).val = (D).germEdge Germ[e,side].val :=
      congrArg Subtype.val (((D).boundaryEnd_bank_eq_iff retain _ _).mpr (Or.inr rfl))
    change (D).boundaryBankLength ((D).boundaryTurn retain Germ[e,side]) = _
    rw [(D).boundaryBankLength_eq_edge, tag, ← (D).boundaryBankLength_eq_edge]
    exact side_eq

/-- The germs specify the order and normalization of the two rays of a roof sector. -/
theorem contourRoofVertex_markedSectorGerm_of_germs
    (p q : Child) (ps qs pt qt : Bool) (j : Fin (S.contour.length + 1))
    (first : Outward p ps pt = (D).boundaryMate retain (S.contour.cycle.point j))
    (last : Outward q qs qt = S.contour.cycle.point j)
    (nonroot : (D).contourOriginalVertex Selection S.contour j ∉ (Fcut).parents.roots)
    (small : (D).totalAngle retain ((D).boundaryEndVertex retain (S.contour.cycle.point j)) <
      2 * Real.pi) :
    let w := (D).boundaryEndVertex retain (S.contour.cycle.point j)
    let mark (b : Bool) (t : unitInterval) :=
      if b then Base (.inl q) qs (finiteSlotParameterize qt t)
      else Base (.inl p) ps (finiteSlotParameterize pt t)
    let length (b : Bool) := if b then BankLength[q] else BankLength[p]
    Nonempty (MarkedSectorGerm CutPoint[w] ((D).totalAngle retain w) mark length) := by
  let w := (D).boundaryEndVertex retain (S.contour.cycle.point j)
  let x := CutPoint[w]
  let θ := (D).totalAngle retain w
  let p₀ := Outward p ps pt
  let q₀ := Outward q qs qt
  have vertex : (D).boundaryEndVertex retain p₀ = w :=
    ((D).boundaryEnd_vertex_eq_iff retain _ _).mpr (Or.inr first)
  have mate : (D).boundaryMate retain p₀ = q₀ :=
    (congrArg ((D).boundaryMate retain) first).trans
      (((D).boundaryMate_involutive retain (S.contour.cycle.point j)).trans last.symm)
  have data := L.contourCutVertex_directed_chart S p₀ (vertex.symm ▸ nonroot) (vertex.symm ▸ small)
  dsimp only at data
  rw [vertex, mate] at data
  obtain ⟨r, positive, chart, first_trace, last_trace⟩ := data
  let edge (b : Bool) := if b then q₀ else p₀
  let mark (b : Bool) (t : unitInterval) :=
    if b then Base (.inl q) qs (finiteSlotParameterize qt t)
    else Base (.inl p) ps (finiteSlotParameterize pt t)
  let length (b : Bool) := if b then BankLength[q] else BankLength[p]
  have parametrized (b : Bool) (t : unitInterval) :
      mark b t = intoCut ((D).directedBoundaryPath (edge b) t) := by
    cases b
    · exact L.contourFiniteRoofGerm_mark S p ps pt t
    · exact L.contourFiniteRoofGerm_mark S q qs qt t
  have speed (b : Bool) : (D).boundaryBankLength (edge b) = length b := by
    cases b
    · exact contourRoof_endpoint_length S p ps pt
    · exact contourRoof_endpoint_length S q qs qt
  have at_w (b : Bool) : (D).boundaryEndVertex retain (edge b) = w := by
    cases b
    · exact vertex
    · exact congrArg ((D).boundaryEndVertex retain) last
  have at_zero (b : Bool) : intoCut ((D).directedBoundaryPath (edge b) 0) = x :=
    congrArg intoCut (((D).directedBoundaryPath_zero (edge b)).trans
      (congrArg ((D).vertexPoint retain) (at_w b)))
  have distance (b : Bool) (t : unitInterval) :
      edist (mark b t) x = ENNReal.ofReal (t.val * length b) := by
    rw [parametrized, ← at_zero b, L.fineMeshWholeMap_edist_bank,
      (T).pairedFolding.edist_directedBoundaryPath_eq_length, speed, edist_dist,
      ENNReal.ofReal_mul t.property.1, mul_comm]
    congr 1
    apply congrArg ENNReal.ofReal
    change dist t.val 0 = t.val
    rw [Real.dist_eq, sub_zero, abs_of_nonneg t.property.1]
  have centered : (chart ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩).val =
      closedAngularSectorOrigin ((D).totalAngle_pos retain w).le := by
    have near : edist (intoCut ((D).directedBoundaryPath p₀ 0)) x < ENNReal.ofReal r := by
      rw [show intoCut ((D).directedBoundaryPath p₀ 0) = x from at_zero false, edist_self]
      exact ENNReal.ofReal_pos.mpr positive
    have eq : (⟨intoCut ((D).directedBoundaryPath p₀ 0), near⟩ : Metric.eball x (ENNReal.ofReal r)) =
        ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩ :=
      Subtype.ext (at_zero false)
    apply PolygonalPoint.ext
    rw [← eq, first_trace 0 near]
    simp [closedAngularSectorOrigin]
  refine ⟨⟨⟨(D).totalAngle_pos retain w, r, positive, chart, centered⟩, distance, ?_⟩⟩
  intro b t near
  have is_near : edist (intoCut ((D).directedBoundaryPath (edge b) t)) x < ENNReal.ofReal r :=
    (congrArg (edist · x) (parametrized b t)).symm.trans_lt near
  have same : (⟨mark b t, near⟩ : Metric.eball x (ENNReal.ofReal r)) =
      ⟨intoCut ((D).directedBoundaryPath (edge b) t), is_near⟩ := Subtype.ext (parametrized b t)
  change (chart ⟨mark b t, near⟩).val.val = (t.val * length b) • polarRay (if b then θ else 0)
  rw [same, ← speed]
  cases b
  · simpa only [edge, ite_false, Bool.false_eq_true, polarRay_zero, Complex.real_smul, mul_one]
      using first_trace t is_near
  · exact last_trace t is_near



/-- The two returns of a genuine child bound a sector strictly smaller than one turn. -/
theorem contourRoofWedge_markedSectorGerm
    (old new : Child) (j : Fin (S.contour.length + 1))
    (after_old : finRotate (S.contour.length + 1) ((D).contourParentInterval Selection S.contour
      (Fcut).boundary_roots S.starts old.val old.property).leave = j)
    (before_new : ((D).contourParentInterval Selection S.contour (Fcut).boundary_roots S.starts
      new.val new.property).enter = j)
    (nonroot : (D).contourOriginalVertex Selection S.contour j ∉ (Fcut).parents.roots) :
    let w := (D).boundaryEndVertex retain (S.contour.cycle.point j)
    let edge (side : Bool) := if side then new else old
    Nonempty (MarkedSectorGerm CutPoint[w] ((D).totalAngle retain w)
      (fun side t => Base (.inl (edge side)) side (unitInterval.symm t))
      (fun side => BankLength[edge side])) := by
  let w := (D).boundaryEndVertex retain (S.contour.cycle.point j)
  let v := Forget[w]
  let A := (D).contourParentInterval Selection S.contour (Fcut).boundary_roots S.starts
    old.val old.property
  let z := (D).boundaryEndVertex retain (S.contour.cycle.point A.enter)
  have germ₁ : Outward old false true = (D).boundaryMate retain (S.contour.cycle.point j) := by
    rw [← after_old]
    have step := S.contour.next_cyclic (D) A.leave
    exact ((D).boundaryMate_involutive retain _).symm.trans
      (congrArg ((D).boundaryMate retain) step)
  have germ₂ : Outward new true true = S.contour.cycle.point j := by
    rw [← before_new]
    change (D).boundaryTurn retain ((D).boundaryTurn retain
      (S.contour.cycle.point ((D).contourParentInterval Selection S.contour (Fcut).boundary_roots
        S.starts new.val new.property).enter)) = _
    exact (D).boundaryTurn_involutive retain _
  have at_parent : v = (Fcut).parents.parent old.val :=
    (congrArg ((D).contourOriginalVertex Selection S.contour) after_old).symm.trans
      ((congrArg (fun x : (D).Vertex retain => Forget[x])
        ((D).contourParentBank_finish_copies Selection S.contour (Fcut).boundary_roots S.starts
          old.val old.property).2).symm.trans
            ((D).contourParentBank_finish Selection S.contour (Fcut).boundary_roots S.starts
              old.val old.property false))
  obtain ⟨advance, start_parent, _, _⟩ := (D).contourChild_consecutive_parent_visits Selection
    S.contour (Fcut).boundary_roots S.starts old.val old.property (at_parent ▸ nonroot)
  have other : z ≠ w := by
    intro same
    have eq := (D).boundaryCycle_vertices_injective retain S.contour.cycle S.contour.closes same
    have rank := congrArg Fin.val (eq.trans after_old.symm)
    change A.enter.val = (finRotate (S.contour.length + 1) A.leave).val at rank
    change (finRotate (S.contour.length + 1) A.leave).val = A.leave.val + 1 at advance
    have before := A.ordered
    omega
  have original : Forget[z] = Forget[w] := start_parent.trans at_parent.symm
  have internal : ¬ (D).IsBoundaryVertex Set.univ v := fun b => nonroot ((Fcut).boundary_roots b)
  have small : (D).totalAngle retain w < 2 * Real.pi :=
    ((D).totalAngle_lt_forgetCuts_of_other_copy (Set.subset_univ retain) w z other.symm original).trans_le
      ((Q).totalAngle_le_two_pi v internal)
  have chart := L.contourRoofVertex_markedSectorGerm_of_germs S old new false true true true j
    germ₁ germ₂ nonroot small
  dsimp only at chart ⊢
  have marks : (fun (b : Bool) (t : unitInterval) =>
      if b then Base (.inl new) true (finiteSlotParameterize true t)
      else Base (.inl old) false (finiteSlotParameterize true t)) =
      (fun b t => Base (.inl (if b then new else old)) b (unitInterval.symm t)) := by
    funext b t
    cases b <;> rfl
  have lengths : (fun (b : Bool) => if b then BankLength[new] else BankLength[old]) =
      (fun b => BankLength[(if b then new else old)]) := by
    funext b
    cases b <;> rfl
  rw [← marks, ← lengths]
  exact chart

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
