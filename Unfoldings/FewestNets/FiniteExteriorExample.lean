module

public import Unfoldings.FewestNets.CheckedExteriorSide
public import Unfoldings.FewestNets.FiniteVisualSideBounds

/-! The first record's saved exterior witnesses on all six sides. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeshStar

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

def q100FirstExteriorPairs : Fin 6 → Fin 48 × Fin 48 :=
  ![(11, 35), (15, 39), (32, 8), (35, 11), (39, 15), (8, 32)]

def checkQ100FirstGamma : CheckedReal certificateDenominator (0.0073243 : ℝ) :=
  (CheckedReal.rat certificateDenominator 0.0073243).convert (by norm_num)

def checkQ100FirstExterior (i : Fin 6) (sign : Bool) : Bool :=
  let pair := q100FirstExteriorPairs i
  checkExteriorWitness certificateDenominator_pos sign (checkedQ100FirstNormal i)
    (checkQ100FirstCorner (i - 1)) (checkQ100FirstCorner i)
    (checkQ100FirstBody (if sign then pair.1 else pair.2)) checkQ100FirstGamma

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Each actual side uses two endpoint tests for each of its two saved witnesses.
theorem q100FirstExterior_pass (i : Fin 6) (sign : Bool) :
    checkQ100FirstExterior i sign = true := by
  fin_cases i <;> cases sign <;> decide +kernel

/-- The pair of certified witnesses controls every direction in the exterior
history cone on the fully closed side. -/
theorem exteriorMargin_q100_face_one_one (i : Fin 6) (unit : ‖q100FirstNormal i‖ = 1)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) (d : Plane)
    (cone : ∀ j : Fin 48,
      0 ≤ inner ℝ
        (AffineMap.lineMap (q100FirstCorner (i - 1)) (q100FirstCorner i) t - q100FirstBody j) d) :
    0.0073243 * ‖d‖ ≤ inner ℝ (q100FirstNormal i) d := by
  let pair := q100FirstExteriorPairs i
  let pos := certificateDenominator_pos
  let cp := checkQ100FirstCorner (i - 1)
  let cq := checkQ100FirstCorner i
  let cn := checkedQ100FirstNormal i
  obtain ⟨del₁, pos₁, upper₁, tan₁, ratio₁⟩ := exteriorWitness_of_check pos true cn cp cq
    (checkQ100FirstBody pair.1) checkQ100FirstGamma (q100FirstExterior_pass i true) ht
  obtain ⟨del₂, pos₂, upper₂, tan₂, ratio₂⟩ := exteriorWitness_of_check pos false cn cp cq
    (checkQ100FirstBody pair.2) checkQ100FirstGamma (q100FirstExterior_pass i false) ht
  simp only [SideVisualWitness.signedCot, Bool.false_eq_true, ite_false] at tan₂
  exact exterior_margin_of_witnesses certificateOrientation unit (by norm_num) del₁ del₂
    pos₁ pos₂ upper₁ upper₂ tan₁ (le_neg_of_le_neg tan₂) (cone pair.1) (cone pair.2) ratio₁ ratio₂

end Unfoldings.FewestNets
