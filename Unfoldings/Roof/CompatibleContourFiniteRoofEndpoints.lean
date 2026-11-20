module

public import Unfoldings.Roof.CompatibleContourSourceOnlyRoofWedgeMarks
public import Unfoldings.Roof.CompatibleContourSourceOnlyFiniteSlotRadii

/-! Exact normalized roof marks at arbitrary first or last endpoints of finite banks. -/

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

local instance finiteRoofEndpointMeshFintype : Fintype (T).Index :=
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

local instance finiteRoofEndpointWholeFintype : Fintype W.Index := W.finiteIndex

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
local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute


local notation "Turn" => TriangleComplex.boundaryTurn D Retain

/-- The outward germ of a finite original bank at its chosen endpoint. -/
def compatibleContourFiniteRoofGerm (e : Edge) (side finish : Bool) :
    (T).pairedComplex.BoundaryEnd (Fcut).retain :=
  if finish then Turn BankAt[e,side] else BankAt[e,side]

local notation "Germ" => K.compatibleContourFiniteRoofGerm compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts

/-- A normalized original roof bank begins at its named outward germ. -/
theorem compatibleContourFiniteRoofGerm_mark (e : Edge) (side finish : Bool) (t : unitInterval) :
    Base (.inl e) side (finiteSlotParameterize finish t) =
      Map ((D).directedBoundaryPath (Germ e side finish) t) := by
  cases finish
  · rfl
  · exact congrArg Map ((D).directedBoundaryPath_turn BankAt[e,side] t).symm

private theorem compatibleContourFiniteRoofGerm_injective :
    Function.Injective (fun a : Edge × Bool × Bool => Germ a.1 a.2.1 a.2.2) := by
  let tag (g : (D).BoundaryEnd Retain) := ((D).boundaryEndEquiv Retain g).1
  have names (e : Edge) (side finish : Bool) : tag (Germ e side finish) = tag BankAt[e,side] := by
    cases finish
    · rfl
    · exact ((D).boundaryEnd_bank_eq_iff Retain _ _).mpr (Or.inr rfl)
  rintro ⟨e, side, finish⟩ ⟨f, other, end_at⟩ h
  change Germ e side finish = Germ f other end_at at h
  have tags := (names e side finish).symm.trans ((congrArg tag h).trans (names f other end_at))
  have same : (e, side) = (f, other) :=
    (D).contourParentBank_bank_injective Selection contour (Fcut).boundary_roots starts tags
  obtain ⟨ef, ss⟩ := Prod.mk.inj same
  subst f
  subst other
  have time : finish = end_at := by
    cases finish <;> cases end_at
    · rfl
    · exact ((D).boundaryTurn_ne Retain _ h.symm).elim
    · exact ((D).boundaryTurn_ne Retain _ h).elim
    · rfl
  subst end_at
  rfl

set_option maxHeartbeats 900000 in
-- Normalized addresses retain the dependent bank parameter at both endpoints.
/-- All actual roof marks at the given nonroot copy are its two named finite bank endpoints. -/
theorem compatibleContourSourceOnlyRoofVertex_baseMark_iff_of_germs
    (p q : Edge) (ps qs pt qt : Bool) (j : Fin (contour.length + 1))
    (first : Germ p ps pt = (D).boundaryMate Retain (contour.cycle.point j))
    (last : Germ q qs qt = contour.cycle.point j)
    (nonroot : (D).contourOriginalVertex Selection contour j ∉ (Fcut).parents.roots)
    (bank : Attachment) (side : Bool) (t : ParamAt bank) :
    let w := (D).boundaryEndVertex Retain (contour.cycle.point j)
    Base bank side t = Map VertexAt[w] ↔
      ((⟨bank, t⟩ : Σ b : Attachment, ParamAt b) =
          ⟨.inl p, finiteSlotParameterize pt 0⟩ ∧ side = ps) ∨
      ((⟨bank, t⟩ : Σ b : Attachment, ParamAt b) =
          ⟨.inl q, finiteSlotParameterize qt 0⟩ ∧ side = qs) := by
  let w := (D).boundaryEndVertex Retain (contour.cycle.point j)
  let x := Map VertexAt[w]
  have below := K.compatibleContourRoofVertex_height_lt_of_nonroot compact nonempty R no_boundary
    level higher M positive inner_disk beta acute w nonroot
  have named (e : Edge) (s u : Bool) (g : (D).boundaryEndVertex Retain (Germ e s u) = w) :
      Base (.inl e) s (finiteSlotParameterize u 0) = x :=
    (K.compatibleContourFiniteRoofGerm_mark compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W e s u 0).trans
      (congrArg Map (((D).directedBoundaryPath_zero (Germ e s u)).trans
        (congrArg ((D).vertexPoint Retain) g)))
  have select (e : Edge) (s u : Bool) (g : (D).boundaryEndVertex Retain (Germ e s u) = w) :
      (e = p ∧ s = ps ∧ u = pt) ∨ (e = q ∧ s = qs ∧ u = qt) := by
    have injective := K.compatibleContourFiniteRoofGerm_injective compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts
    rcases ((D).boundaryEnd_vertex_eq_iff Retain _ _).mp g with at_last | at_first
    · have eq : (e, s, u) = (q, qs, qt) := injective (at_last.trans last.symm)
      exact Or.inr (by simpa only [Prod.mk.injEq] using eq)
    · have eq : (e, s, u) = (p, ps, pt) := injective (at_first.trans first.symm)
      exact Or.inl (by simpa only [Prod.mk.injEq] using eq)
  constructor
  · intro mark
    cases bank with
    | inr tail =>
      exact (K.compatibleContourRoofVertex_ne_tailMark compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W w below tail side t mark).elim
    | inl e =>
      have ends := (K.compatibleContourRoofVertex_eq_parentMark_iff compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts W w below e side t).mp mark
      rcases ends with ⟨rfl, start⟩ | ⟨rfl, finish⟩
      · rcases select e side false start.symm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
      · rcases select e side true finish.symm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · exact Or.inl ⟨by simp [finiteSlotParameterize], rfl⟩
        · exact Or.inr ⟨by simp [finiteSlotParameterize], rfl⟩
  · let read (s : Bool) (z : Σ b : Attachment, ParamAt b) := Base z.1 s z.2
    rintro (⟨same, tag⟩ | ⟨same, tag⟩)
    · rw [tag]
      exact (congrArg (read ps) same).trans
        (named p ps pt (((D).boundaryEnd_vertex_eq_iff Retain _ _).mpr (Or.inr first)))
    · rw [tag]
      exact (congrArg (read qs) same).trans
        (named q qs qt (congrArg ((D).boundaryEndVertex Retain) last))

end Unfoldings.ConvexRoof
