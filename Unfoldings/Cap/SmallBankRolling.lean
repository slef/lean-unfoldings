module

public import Unfoldings.Cap.JordanCyclicRolling
public import Unfoldings.Geometry.PolygonalClosureEquations

/-! A concrete conclusion about the actual intrinsic rolling of a radial bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

open Classical in
/-- Actual endpoint copies delimit the geometric bank and its intrinsic real heading error.
Every contour and rolling map here is constructed from the original physical cap. -/
def HasSmallRadialBankRolling {n : ℕ} (P : PolygonalChain Plane n) (q c : Plane)
    (jordan : Schoenflies.IsJordanCurve (P.threeSegmentClosure q c)) (η : ℝ) : Prop :=
  ∃ (contained : P.threeSegmentClosure q c ⊆ interior K.footprint)
    (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) (P.threeSegmentClosure q c)),
    ∃ first last :
        Fin ((K.jordanContour jordan (contained.trans interior_subset) avoids).length + 1),
      ({K.jordanBankPosition jordan (contained.trans interior_subset) avoids first,
        K.jordanBankPosition jordan (contained.trans interior_subset) avoids last} : Finset Plane) =
          {P.vertex 0, P.vertex (Fin.last n)} ∧
      K.jordanContourBankOn jordan (contained.trans interior_subset) avoids
        (Set.range P.path) first ∧
      ¬ K.jordanContourBankOn jordan (contained.trans interior_subset) avoids
        (Set.range P.path) last ∧
      |K.jordanCyclicRollHeadingError jordan (contained.trans interior_subset) avoids first
        ⟨((finCycle first).symm last).val - 1, by omega⟩| < η

end Unfoldings.ConvexCap
