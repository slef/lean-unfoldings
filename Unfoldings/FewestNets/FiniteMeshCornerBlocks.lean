module

public import Unfoldings.FewestNets.FiniteMeshCornerExample
public import Unfoldings.FewestNets.FiniteMeshPerimeterBlockSum

/-! Reusable block checks for the finite network's outward normals and corner geometry. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeshStar Real

namespace MeshStar.Checked

variable {D n : ℕ} {star : MeshStar (n + 1)} (a : Checked D star)

def checkAllCorners (hD : 0 < D) {r ψ : ℝ}
    (cr : CheckedReal D (tan r)) (cψ : CheckedReal D (cos ψ)) : Bool :=
  (List.finRange (n + 1)).all fun j =>
    (a.dualOffset hD j).isPositive && a.checkCorner hD cr cψ j

theorem checkAllCorners_sound (hD : 0 < D) {r ψ : ℝ}
    (cr : CheckedReal D (tan r)) (cψ : CheckedReal D (cos ψ))
    (h : a.checkAllCorners hD cr cψ = true) (j : Fin (n + 1)) :
    0 < inner ℝ star.direction (star.dual j) ∧
      tan r < meshCornerAltitude (star.cornerRay j (j - 1)) (star.cornerRay j (j + 1)) ∧
      meshCornerCosine (star.cornerRay j (j - 1)) (star.cornerRay j (j + 1)) < cos ψ := by
  have check := List.all_eq_true.mp h j (List.mem_finRange j)
  rw [Bool.and_eq_true] at check
  exact ⟨CheckedReal.positive_of_isPositive hD _ check.1,
    a.corner_bounds_of_check hD cr cψ j check.2⟩

end MeshStar.Checked

def checkFaceCornerBlock (q blockSize block denominator degrees : ℕ) : Bool :=
  let r := checkGuardTangent certificateDenominator_pos denominator
  let a := checkIncidentCosine certificateDenominator_pos degrees
  (faceMeshKeyBlock q blockSize block).all fun key =>
    (checkFace certificateDenominator_pos q key.1 key.2).checkAllCorners
      certificateDenominator_pos r a

def checkSeamCornerBlock (q blockSize block denominator degrees : ℕ) : Bool :=
  let r := checkGuardTangent certificateDenominator_pos denominator
  let a := checkIncidentCosine certificateDenominator_pos degrees
  (seamMeshKeyBlock q blockSize block).all fun key =>
    (checkSeam certificateDenominator_pos q key).checkAllCorners certificateDenominator_pos r a

def checkPentagonCorners (q denominator degrees : ℕ) : Bool :=
  (checkPentagon certificateDenominator_pos q).checkAllCorners certificateDenominator_pos
    (checkGuardTangent certificateDenominator_pos denominator)
    (checkIncidentCosine certificateDenominator_pos degrees)

end Unfoldings.FewestNets
