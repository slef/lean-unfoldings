module

public import Unfoldings.Roof.CompatibleContourGraftExactness
public import Unfoldings.Metric.ClosedSeamRestriction

/-! Unique-mark graft balls retain just their original consecutive bank attachment. -/

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

local notation "inside" => K.compatible_section_interior compact nonempty R level higher M

local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance contourFiniteExcisionMeshFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut

local notation "BankAt[" q "," h "," e "]" =>
  K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e
local notation "OpenedAt[" q "," h "," e "]" =>
  K.compatibleContourOpenedBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e

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
  (models : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    BankGapModel
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourOpenedBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance contourFiniteExcisionWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Pieces" => K.compatibleContourGraftPiece compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour starts W models
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Base" => K.compatibleContourBaseMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Gap" => K.compatibleContourGapMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models

local notation "Index" => K.compatibleContourCellIndex compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Cells" => K.compatibleContourCells compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Inner" => K.compatibleContourCellInner compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Coordinates" => K.compatibleContourCellCoordinates compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "Seams" => K.compatibleContourClosedSeams compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts W models
local notation "Banks" => MetricGluing.bankSeams (MetricGluing.bankStackLeft Pieces Stack Base Gap)
  (MetricGluing.bankStackRight Pieces Stack Base Gap)

local notation "Raw" => MetricGluing.NestedCell (fun i j => Cells i j)
local notation "Original" => MetricGluing.mappedNestedPoint Cells Inner Coordinates
local notation "BankSeams" => K.compatibleContourBankClosedSeams compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "LP" => MetricGluing.bankStackLeftPiece Stack Pieces Base Gap

/-- Keep all original internal seams and just one original consecutive bank attachment. -/
def compatibleContourKeepBankSlot (slot : MetricGluing.BankStackSlot Stack) :
    (Seams).Seam → Prop
  | .inl _ => True
  | .inr bank => bank.1 = slot

local notation "KeepAt[" slot "]" => K.compatibleContourKeepBankSlot compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models slot

/-- Every actual bank domain incident to a unique-mark seam class belongs to its
original consecutive slot. The classification includes all original cell representatives. -/
theorem compatibleContourBankSlot_incident_bank_slot
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (slot : MetricGluing.BankStackSlot Stack)
    (t : K.compatibleContourBankParameter compact nonempty R no_boundary level higher M
      positive inner_disk beta acute slot.1)
    (unique : MetricGluing.BankStackUniqueMarksAt Stack Pieces Base Gap slot.1 t)
    (a : MetricGluing.Total Raw)
    (center : Original a = MetricGluing.bankStackLeft Pieces Stack Base Gap slot t)
    (b : (BankSeams).Seam) (incident : (Seams).Incident a (.inr b)) :
    b.1 = slot := by
  obtain ⟨p, related, u, equal⟩ := incident
  obtain ⟨s, first, _last⟩ := u.property
  have bank_point : Original ⟨(BankSeams).left b, p⟩ =
      MetricGluing.bankStackLeft Pieces Stack Base Gap b.1 s := by
    have replace := congrArg (fun q => Original ⟨(BankSeams).left b, q⟩) equal.symm
    exact replace.trans ((congrArg (Sigma.mk (LP b.1)) first).trans
      (MetricGluing.bankStackLeft_curve Stack Pieces Base Gap b.1 s).symm)
  have points := congrArg
    (K.compatibleContourClosedSeamIsometry compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models)
    (MetricGluing.point_eq_of_eqvGen Raw related)
  change MetricGluing.point Pieces Banks (Original a) =
    MetricGluing.point Pieces Banks (Original ⟨(BankSeams).left b, p⟩) at points
  have metric_equal : MetricGluing.point Pieces Banks
      (MetricGluing.bankStackEndpoint Stack Pieces Base Gap false b.1 s) =
        MetricGluing.point Pieces Banks
          (MetricGluing.bankStackLeft Pieces Stack Base Gap slot t) :=
    (congrArg (MetricGluing.point Pieces Banks) bank_point).symm.trans
      (points.symm.trans (congrArg (MetricGluing.point Pieces Banks) center))
  have named := MetricGluing.bankStackEndpoint_parameter_eq_of_point_eq Stack Pieces Base Gap
    (K.compatibleContourBankStack_nodup compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour)
    (K.compatibleContourGraft_exact compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models geometry) slot t unique false b.1 s metric_equal
  exact congrArg Sigma.fst named

/-- Removing all other bank attachments preserves a whole small metric ball at every
unique-mark seam time. Original internal seams and every cell representative are retained. -/
theorem compatibleContourBankSlot_forgetChart
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (slot : MetricGluing.BankStackSlot Stack)
    (t : K.compatibleContourBankParameter compact nonempty R no_boundary level higher M
      positive inner_disk beta acute slot.1)
    (unique : MetricGluing.BankStackUniqueMarksAt Stack Pieces Base Gap slot.1 t)
    (a : MetricGluing.Total Raw)
    (center : Original a = MetricGluing.bankStackLeft Pieces Stack Base Gap slot t) :
    Nonempty (MetricGluing.ForgetChart Raw
      ((Seams).restrict_relation_included KeepAt[slot]) a) := by
  apply (Seams).exists_forgetChart_restrict KeepAt[slot] a
    (K.compatibleContourClosedSeams_finite_classes compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models geometry a)
  intro s incident
  cases s with
  | inl internal => trivial
  | inr bank =>
    exact K.compatibleContourBankSlot_incident_bank_slot compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W models geometry slot t unique
      a center bank incident

/-- Every actual bank domain incident to an ordinary finite seam class belongs to its
original consecutive slot. The classification includes all original cell representatives. -/
theorem compatibleContourFiniteSeam_incident_bank_slot
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (vertex : {v : (D).Vertex Set.univ // v ∉ (Fcut).parents.roots})
    (i : Fin ((Stack (.inl vertex)).length + 1)) (t : unitInterval) (bounds : 0 < t ∧ t < 1)
    (a : MetricGluing.Total Raw)
    (center : Original a = MetricGluing.bankStackLeft Pieces Stack Base Gap ⟨.inl vertex, i⟩ t)
    (b : (BankSeams).Seam) (incident : (Seams).Incident a (.inr b)) :
    b.1 = ⟨.inl vertex, i⟩ :=
  K.compatibleContourBankSlot_incident_bank_slot compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W models geometry ⟨.inl vertex, i⟩ t
    (K.compatibleContourFiniteMarks_unique compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models geometry vertex t bounds) a center b incident

/-- Removing all other bank attachments preserves a whole small metric ball at every
strict finite seam time. Original internal seams and every cell representative are retained. -/
theorem compatibleContourFiniteSeam_forgetChart
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (vertex : {v : (D).Vertex Set.univ // v ∉ (Fcut).parents.roots})
    (i : Fin ((Stack (.inl vertex)).length + 1)) (t : unitInterval) (bounds : 0 < t ∧ t < 1)
    (a : MetricGluing.Total Raw)
    (center : Original a = MetricGluing.bankStackLeft Pieces Stack Base Gap ⟨.inl vertex, i⟩ t) :
    Nonempty (MetricGluing.ForgetChart Raw
      ((Seams).restrict_relation_included KeepAt[⟨.inl vertex, i⟩]) a) :=
  K.compatibleContourBankSlot_forgetChart compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W models geometry ⟨.inl vertex, i⟩ t
    (K.compatibleContourFiniteMarks_unique compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models geometry vertex t bounds) a center

end Unfoldings.ConvexRoof
