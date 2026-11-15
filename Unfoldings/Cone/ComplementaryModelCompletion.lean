module

public import Unfoldings.Cone.ComplementarySectorPlane
public import Unfoldings.Metric.Reparametrize

/-! Complete an original intrinsic corner model by its actual complementary geometric sector. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

universe u

variable {X : Type u} [EMetricSpace X] {width : ℝ}
  (E : X ≃ᵢ PolygonalPoint (closedAngularSector width))

/-- Keep the original corner space as one whole metric piece. -/
def complementaryModelCell (X : Type u) (width : ℝ) : Bool → Type u
  | false => X
  | true => ULift.{u} (PolygonalPoint (complementarySector width))

/-- Universe lifting only changes representation, never the added sector metric. -/
instance complementarySector_ulift_emetric (width : ℝ) :
    EMetricSpace (ULift.{u} (PolygonalPoint (complementarySector width))) :=
  EMetricSpace.induced ULift.down ULift.down_injective inferInstance

instance complementaryModelCell_emetric (b : Bool) :
    EMetricSpace (complementaryModelCell X width b) := by
  cases b <;> dsimp [complementaryModelCell] <;> infer_instance

/-- Only coordinates change; the original corner metric remains intact. -/
def complementaryModelCoordinates (b : Bool) : complementaryModelCell X width b ≃ᵢ
    PolygonalPoint (complementarySectorRegion width b) :=
  match b with
  | false => E
  | true =>
    { toFun := ULift.down
      invFun := ULift.up
      left_inv := by rintro ⟨x⟩; rfl
      right_inv := fun _ => rfl
      isometry_toFun := fun _ _ => rfl }

/-- Identify the two original bank rays at equal physical coordinates. -/
def complementaryModelGlue :=
  MetricGluing.reparametrizeGlue (complementaryModelCoordinates E)
    (MetricGluing.polygonalCoincident (complementarySectorRegion width))

abbrev ComplementaryModelCompletion :=
  MetricGluing.Realization (complementaryModelCell X width) (complementaryModelGlue E)

def complementaryModelOriginal (x : X) : ComplementaryModelCompletion E :=
  MetricGluing.of (complementaryModelCell X width) (complementaryModelGlue E) false x

def complementaryModelGap (x : PolygonalPoint (complementarySector width)) :
    ComplementaryModelCompletion E :=
  MetricGluing.of (complementaryModelCell X width) (complementaryModelGlue E) true ⟨x⟩

/-- Completing either a convex or reentrant original corner gives the exact whole-plane
metric. No width is required to be below a half-turn. -/
def complementaryModelPlaneIsometryEquiv (positive : 0 < width) (small : width < 2 * Real.pi) :
    ComplementaryModelCompletion E ≃ᵢ ℂ :=
  (MetricGluing.reparametrizeIsometryEquiv (complementaryModelCoordinates E)
    (MetricGluing.polygonalCoincident (complementarySectorRegion width))).trans
      (complementarySectorPlaneIsometryEquiv width positive small)

@[simp] theorem complementaryModelPlane_original (positive : 0 < width)
    (small : width < 2 * Real.pi) (x : X) :
    complementaryModelPlaneIsometryEquiv E positive small (complementaryModelOriginal E x) =
      (E x).val := rfl

@[simp] theorem complementaryModelPlane_gap (positive : 0 < width)
    (small : width < 2 * Real.pi) (x : PolygonalPoint (complementarySector width)) :
    complementaryModelPlaneIsometryEquiv E positive small (complementaryModelGap E x) =
      x.val := rfl

/-- All and only the intended two equal-radius banks are identified across the two pieces. -/
theorem complementaryModelCompletion_cross_banks (positive : 0 < width)
    (small : width < 2 * Real.pi) (x : X) (y : PolygonalPoint (complementarySector width)) :
    complementaryModelOriginal E x = complementaryModelGap E y ↔
      ∃ r : ℝ≥0, ((E x).val = (r : ℂ) ∧ y.val = (r : ℂ)) ∨
        ((E x).val = (r : ℂ) * polarRay width ∧ y.val = (r : ℂ) * polarRay width) := by
  constructor
  · intro equal
    have physical : (E x).val = y.val := congrArg
      (complementaryModelPlaneIsometryEquiv E positive small) equal
    have both : (E x).val ∈ closedAngularSector width ∩ complementarySector width :=
      ⟨(E x).property, physical ▸ y.property⟩
    rw [closedAngularSector_inter_complementary width positive small] at both
    rcases both with ⟨r, first⟩ | ⟨r, last⟩
    · exact ⟨r, Or.inl ⟨first.symm, physical.symm.trans first.symm⟩⟩
    · exact ⟨r, Or.inr ⟨last.symm, physical.symm.trans last.symm⟩⟩
  · rintro ⟨r, pair⟩
    apply MetricGluing.point_eq_of_glue
    exact pair.elim (fun h => h.1.trans h.2.symm) (fun h => h.1.trans h.2.symm)

end Unfoldings
