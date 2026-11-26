module

public import Unfoldings.FewestNets.ThreeExitRoofVertexCharts
public import Unfoldings.FewestNets.ThreeExitGraftPhysicalAddresses
public import Unfoldings.Roof.SelectedParentEndpoint
public import Unfoldings.Complex.ContourBetweenChildBlocks
public import Unfoldings.Roof.CompatibleContourSourceOnlyFiniteSlotRadii

/-! The two contour marks incident to each original roof corner. -/

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

local instance wholeCutVertexMarksIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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

/-- A finite bank meets a specified retained corner only at one of its exact endpoint copies. -/
theorem contourRoofVertex_eq_parentMark_iff
    (w : (D).Vertex retain) (nonroot : Forget[w] ∉ (Fcut).parents.roots)
    (e : Child) (side : Bool) (t : unitInterval) :
    Base (.inl e) side t = CutPoint[w] ↔
      (t = 0 ∧ w = (D).boundaryEndVertex retain Germ[e,side]) ∨
        (t = 1 ∧ w = (D).boundaryEndVertex retain ((D).boundaryTurn retain Germ[e,side])) := by
  let bank := Germ[e,side]
  constructor
  · intro equal
    have same := congrArg (fun x : L.whole.Cut => Cap.horizontal (restore x).val) equal
    rw [L.contourPhysicalAddress_side, L.contourPhysicalAddress_finite,
      L.restore_fineMeshWholeMap] at same
    have position : (T).pairedFolding.toSpace retain ((D).vertexPoint retain w) =
        (T).pairedFolding.toSpace Set.univ ((D).vertexPoint Set.univ Forget[w]) := by
      rw [(D).vertexPoint_vertexForgetCuts, (T).pairedFolding.toSpace_forgetCuts]
    rw [position] at same
    have endpoints := (Q).selectedParentLineMap_eq_vertex Selection e Forget[w] t same
    have point := L.fineMeshWholeMap_injective_at S.higher ((D).vertexPoint retain w)
      ((D).directedBoundaryPath bank t) (L.contourCutVertex_below S w nonroot) equal.symm
    rcases endpoints with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inl ⟨rfl, (D).vertexPoint_injective retain (point.trans ((D).directedBoundaryPath_zero bank))⟩
    · exact Or.inr ⟨rfl, (D).vertexPoint_injective retain (point.trans ((D).directedBoundaryPath_one bank))⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact congrArg intoCut ((D).directedBoundaryPath_zero bank)
    · exact congrArg intoCut ((D).directedBoundaryPath_one bank)

/-- A nonroot retained corner is separate from every marked point on a continued exit. -/
theorem contourRoofVertex_ne_tailMark (w : (D).Vertex retain)
    (nonroot : Forget[w] ∉ (Fcut).parents.roots)
    (e : Exit) (side : Bool) (t : ℝ≥0) :
    Base (.inr e) side t ≠ CutPoint[w] := by
  intro equal
  obtain ⟨speed, positive, heights⟩ := L.exists_contourPhysicalAddress_tail_height S e
  have same := congrArg (fun x : L.whole.Cut => (G).height (Cap.horizontal (restore x).val)) equal
  change (G).height (Cap.horizontal (restore (Base (.inr e) side t)).val) = _ at same
  rw [L.contourPhysicalAddress_side, heights] at same
  exact (not_lt_of_ge ((le_add_of_nonneg_right (mul_nonneg positive.le t.property)).trans_eq same))
    (L.contourCutVertex_below S w nonroot)

/-- The outward germ of a finite original bank at its chosen endpoint. -/
def contourFiniteRoofGerm (e : Child) (side finish : Bool) :
    (D).BoundaryEnd retain :=
  if finish then (D).boundaryTurn retain Germ[e,side] else Germ[e,side]

local notation "Outward" => contourFiniteRoofGerm S

/-- A normalized original roof bank begins at its named outward germ. -/
theorem contourFiniteRoofGerm_mark (e : Child) (side finish : Bool) (t : unitInterval) :
    Base (.inl e) side (finiteSlotParameterize finish t) =
      intoCut ((D).directedBoundaryPath (Outward e side finish) t) := by
  cases finish
  · rfl
  · exact congrArg intoCut ((D).directedBoundaryPath_turn Germ[e,side] t).symm

private theorem contourFiniteRoofGerm_injective :
    Function.Injective (fun a : Child × Bool × Bool => Outward a.1 a.2.1 a.2.2) := by
  let tag (g : (D).BoundaryEnd retain) := ((D).boundaryEndEquiv retain g).1
  have names (e : Child) (side finish : Bool) : tag (Outward e side finish) = tag Germ[e,side] := by
    cases finish
    · rfl
    · exact ((D).boundaryEnd_bank_eq_iff retain _ _).mpr (Or.inr rfl)
  rintro ⟨e, side, finish⟩ ⟨f, other, end_at⟩ h
  change Outward e side finish = Outward f other end_at at h
  have tags := (names e side finish).symm.trans ((congrArg tag h).trans (names f other end_at))
  have same : (e, side) = (f, other) :=
    (D).contourParentBank_bank_injective Selection S.contour (Fcut).boundary_roots S.starts tags
  obtain ⟨ef, ss⟩ := Prod.mk.inj same
  subst f
  subst other
  have time : finish = end_at := by
    cases finish <;> cases end_at
    · rfl
    · exact ((D).boundaryTurn_ne retain _ h.symm).elim
    · exact ((D).boundaryTurn_ne retain _ h).elim
    · rfl
  subst end_at
  rfl

set_option maxHeartbeats 900000 in
-- Normalized addresses retain the dependent bank parameter at both endpoints.
/-- All actual roof marks at the given nonroot copy are its two named finite bank endpoints. -/
theorem contourRoofVertex_baseMark_iff_of_germs
    (p q : Child) (ps qs pt qt : Bool) (j : Fin (S.contour.length + 1))
    (first : Outward p ps pt = (D).boundaryMate retain (S.contour.cycle.point j))
    (last : Outward q qs qt = S.contour.cycle.point j)
    (nonroot : (D).contourOriginalVertex Selection S.contour j ∉ (Fcut).parents.roots)
    (bank : Attachment) (side : Bool) (t : Param bank) :
    let w := (D).boundaryEndVertex retain (S.contour.cycle.point j)
    Base bank side t = intoCut ((D).vertexPoint retain w) ↔
      ((⟨bank, t⟩ : Σ b : Attachment, Param b) =
          ⟨.inl p, finiteSlotParameterize pt 0⟩ ∧ side = ps) ∨
      ((⟨bank, t⟩ : Σ b : Attachment, Param b) =
          ⟨.inl q, finiteSlotParameterize qt 0⟩ ∧ side = qs) := by
  let w := (D).boundaryEndVertex retain (S.contour.cycle.point j)
  let x := intoCut ((D).vertexPoint retain w)
  have named (e : Child) (s u : Bool) (g : (D).boundaryEndVertex retain (Outward e s u) = w) :
      Base (.inl e) s (finiteSlotParameterize u 0) = x :=
    (L.contourFiniteRoofGerm_mark S e s u 0).trans
      (congrArg intoCut (((D).directedBoundaryPath_zero (Outward e s u)).trans
        (congrArg ((D).vertexPoint retain) g)))
  have select (e : Child) (s u : Bool) (g : (D).boundaryEndVertex retain (Outward e s u) = w) :
      (e = p ∧ s = ps ∧ u = pt) ∨ (e = q ∧ s = qs ∧ u = qt) := by
    have injective := contourFiniteRoofGerm_injective S
    rcases ((D).boundaryEnd_vertex_eq_iff retain _ _).mp g with at_last | at_first
    · have eq : (e, s, u) = (q, qs, qt) := injective (at_last.trans last.symm)
      exact Or.inr (by simpa only [Prod.mk.injEq] using eq)
    · have eq : (e, s, u) = (p, ps, pt) := injective (at_first.trans first.symm)
      exact Or.inl (by simpa only [Prod.mk.injEq] using eq)
  constructor
  · intro mark
    cases bank with
    | inr tail =>
      exact (L.contourRoofVertex_ne_tailMark S w nonroot tail side t mark).elim
    | inl e =>
      have ends := (L.contourRoofVertex_eq_parentMark_iff S w nonroot e side t).mp mark
      rcases ends with ⟨rfl, start⟩ | ⟨rfl, finish⟩
      · rcases select e side false start.symm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
      · rcases select e side true finish.symm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · exact Or.inl ⟨by simp [finiteSlotParameterize], rfl⟩
        · exact Or.inr ⟨by simp [finiteSlotParameterize], rfl⟩
  · let read (s : Bool) (z : Σ b : Attachment, Param b) := Base z.1 s z.2
    rintro (⟨same, tag⟩ | ⟨same, tag⟩)
    · rw [tag]
      exact (congrArg (read ps) same).trans
        (named p ps pt (((D).boundaryEnd_vertex_eq_iff retain _ _).mpr (Or.inr first)))
    · rw [tag]
      exact (congrArg (read qs) same).trans
        (named q qs qt (congrArg ((D).boundaryEndVertex retain) last))

/-- A particular final roof wedge records both incident child bank copies, and no other
original attachment marks meet its center. -/
theorem contourRoofWedge_baseMark_iff
    (old_child new_child : Child) (j : Fin (S.contour.length + 1))
    (after_old : finRotate (S.contour.length + 1) ((D).contourParentInterval Selection S.contour
      (Fcut).boundary_roots S.starts old_child.val old_child.property).leave = j)
    (before_new : ((D).contourParentInterval Selection S.contour (Fcut).boundary_roots S.starts
      new_child.val new_child.property).enter = j)
    (nonroot : (D).contourOriginalVertex Selection S.contour j ∉ (Fcut).parents.roots)
    (bank : Attachment) (side : Bool) (t : Param bank) :
    let w := (D).boundaryEndVertex retain (S.contour.cycle.point j)
    Base bank side t = intoCut ((D).vertexPoint retain w) ↔
      (⟨bank, t⟩ : Σ b : Attachment, Param b) = ⟨.inl old_child, 1⟩ ∧ side = false ∨
      (⟨bank, t⟩ : Σ b : Attachment, Param b) = ⟨.inl new_child, 1⟩ ∧ side = true := by
  let w := (D).boundaryEndVertex retain (S.contour.cycle.point j)
  have germs := (D).contour_parent_wedge_end_eq_iff Selection S.contour (Fcut).boundary_roots
    S.starts old_child new_child j after_old before_new
  have tags : Function.Injective (fun p : Child × Bool =>
      Germ[p.1,p.2]) :=
    (D).contourParentBank_injective Selection S.contour (Fcut).boundary_roots S.starts
  have no_reverse (a b : Child) (x y : Bool) :
      Germ[a,x] ≠ (D).boundaryTurn retain Germ[b,y] := by
    intro h
    have equal := ((D).boundaryEnd_bank_eq_iff retain _ _).mpr (Or.inr h)
    have same : (a, x) = (b, y) :=
      (D).contourParentBank_bank_injective Selection S.contour (Fcut).boundary_roots S.starts equal
    cases same
    exact (D).boundaryTurn_ne retain Germ[a,x] h.symm
  constructor
  · intro mark
    cases bank with
    | inr tail => exact (L.contourRoofVertex_ne_tailMark S w nonroot tail side t mark).elim
    | inl e =>
      have ends := (L.contourRoofVertex_eq_parentMark_iff S w nonroot e side t).mp mark
      rcases ends with ⟨rfl, start⟩ | ⟨rfl, finish⟩
      · rcases (germs _).mp start.symm with old | new
        · exact (no_reverse _ _ _ _ old).elim
        · exact (no_reverse _ _ _ _ new).elim
      · rcases (germs _).mp finish.symm with old | new
        · have same : (e, side) = (old_child, false) :=
            tags (((D).boundaryTurn_involutive retain).injective old)
          cases same
          exact Or.inl ⟨rfl, rfl⟩
        · have same : (e, side) = (new_child, true) :=
            tags (((D).boundaryTurn_involutive retain).injective new)
          cases same
          exact Or.inr ⟨rfl, rfl⟩
  · rintro (⟨same, rfl⟩ | ⟨same, rfl⟩)
    · cases same
      exact (L.contourRoofVertex_eq_parentMark_iff S w nonroot old_child false 1).mpr
        (Or.inr ⟨rfl, ((germs _).mpr (Or.inl rfl)).symm⟩)
    · cases same
      exact (L.contourRoofVertex_eq_parentMark_iff S w nonroot new_child true 1).mpr
        (Or.inr ⟨rfl, ((germs _).mpr (Or.inr rfl)).symm⟩)

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
