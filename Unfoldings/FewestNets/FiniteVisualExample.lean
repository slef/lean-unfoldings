module

public import Unfoldings.FewestNets.CheckedMeshChart
public import Unfoldings.FewestNets.CheckedVisualSide
public import Unfoldings.FewestNets.FiniteDevelopmentExample

/-! The rational progress body and visual witnesses of the first frequency-100 face key. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry Real MeshStar

/-- The coordinates used in the paper's finite-q100 certificate at key (1, 1). -/
def q100FirstBodyCoordinates : Fin 48 → ℚ × ℚ :=
  ![
    (-585693/1000000, -5753/250000),
    (-578791/1000000, -8563/125000),
    (-565983/1000000, -112581/1000000),
    (-110571/200000, -155921/1000000),
    (-269557/500000, -19889/100000),
    (-524437/1000000, -241769/1000000),
    (-25401/50000, -56901/200000),
    (-489369/1000000, -163493/500000),
    (-379431/1000000, -283929/500000),
    (-338041/1000000, -18863/31250),
    (-281283/1000000, -12203/20000),
    (-226071/1000000, -612793/1000000),
    (226071/1000000, -612793/1000000),
    (281283/1000000, -12203/20000),
    (338041/1000000, -18863/31250),
    (379431/1000000, -283929/500000),
    (7647/15625, -81753/250000),
    (508041/1000000, -284517/1000000),
    (524437/1000000, -241769/1000000),
    (269557/500000, -19889/100000),
    (110571/200000, -155921/1000000),
    (565983/1000000, -112581/1000000),
    (578791/1000000, -8563/125000),
    (585693/1000000, -5753/250000),
    (585693/1000000, 5753/250000),
    (578791/1000000, 8563/125000),
    (565983/1000000, 112581/1000000),
    (110571/200000, 155921/1000000),
    (269557/500000, 19889/100000),
    (524437/1000000, 241769/1000000),
    (25401/50000, 56901/200000),
    (489369/1000000, 163493/500000),
    (379431/1000000, 283929/500000),
    (338041/1000000, 18863/31250),
    (281283/1000000, 12203/20000),
    (226071/1000000, 612793/1000000),
    (-226071/1000000, 612793/1000000),
    (-281283/1000000, 12203/20000),
    (-338041/1000000, 18863/31250),
    (-379431/1000000, 283929/500000),
    (-7647/15625, 81753/250000),
    (-508041/1000000, 284517/1000000),
    (-524437/1000000, 241769/1000000),
    (-269557/500000, 19889/100000),
    (-110571/200000, 155921/1000000),
    (-565983/1000000, 112581/1000000),
    (-578791/1000000, 8563/125000),
    (-585693/1000000, 5753/250000)
  ]

def q100FirstBody (i : Fin 48) : Plane :=
  let p := q100FirstBodyCoordinates i
  WithLp.toLp 2 ![(p.1 : ℝ), (p.2 : ℝ)]

def checkQ100FirstBody (i : Fin 48) : CheckedPlane certificateDenominator (q100FirstBody i) :=
  let p := q100FirstBodyCoordinates i
  CheckedPlane.rat certificateDenominator p.1 p.2

/-- Saved signed pair tests, in order along each of the six closed sides. -/
def q100FirstPanels : Fin 6 → List (SideVisualWitness 48) :=
  ![
    [
      ⟨0, 1/4, 15, 33, true⟩,
      ⟨1/4, 1/2, 24, 35, true⟩,
      ⟨1/2, 3/4, 25, 38, true⟩,
      ⟨3/4, 1, 32, 39, true⟩
    ],
    [
      ⟨0, 1/4, 32, 39, true⟩,
      ⟨1/4, 1/2, 33, 46, true⟩,
      ⟨1/2, 3/4, 36, 47, true⟩,
      ⟨3/4, 1, 8, 38, false⟩
    ],
    [
      ⟨0, 1/2, 8, 38, false⟩,
      ⟨1/2, 1, 9, 39, false⟩
    ],
    [
      ⟨0, 1/4, 9, 39, false⟩,
      ⟨1/4, 1/2, 12, 46, false⟩,
      ⟨1/2, 3/4, 1, 14, true⟩,
      ⟨3/4, 1, 8, 15, true⟩
    ],
    [
      ⟨0, 1/4, 8, 15, true⟩,
      ⟨1/4, 1/2, 9, 22, true⟩,
      ⟨1/2, 3/4, 11, 25, true⟩,
      ⟨3/4, 1, 14, 32, true⟩
    ],
    [
      ⟨0, 1/2, 14, 32, true⟩,
      ⟨1/2, 1, 15, 33, true⟩
    ]
  ]

/-- Use the exact derivative-circumradius rescaling of the saved record. -/
def q100FirstCorner (i : Fin 6) : Plane := (face 100 1 1).derivativeNormalizedVertex 100 i

def checkQ100FirstCorner (i : Fin 6) : CheckedPlane certificateDenominator (q100FirstCorner i) :=
  let pos := certificateDenominator_pos
  (checkFace pos 100 1 1).derivativeNormalizedVertex pos 100 i

def checkQ100FirstCot : CheckedReal certificateDenominator (0.1433718319 : ℝ) :=
  (CheckedReal.rat certificateDenominator 0.1433718319).convert (by norm_num)

theorem q100FirstPanels_nonempty (i : Fin 6) : q100FirstPanels i ≠ [] := by
  fin_cases i <;> decide +kernel

theorem q100FirstPanels_cover (i : Fin 6) :
    SideVisualWitness.coversFrom 0 (q100FirstPanels i) = true := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
-- The kernel evaluates all rational endpoint signs for each of the six side covers.
theorem q100FirstPanels_valid (i : Fin 6) :
    (q100FirstPanels i).all (SideVisualWitness.checkPanel certificateDenominator_pos
      checkQ100FirstCot (checkQ100FirstCorner i) (checkQ100FirstCorner (i + 1))
      checkQ100FirstBody) = true := by
  fin_cases i <;> decide +kernel

theorem q100FirstCot_lt :
    0.1433718319 * sin (81.841 * π / 180) < cos (81.841 * π / 180) := by
  have h := cotangent_margin_q100_face_one_one
  rw [show 8.159 * π / 180 = π / 2 - 81.841 * π / 180 by ring,
    sin_pi_div_two_sub, cos_pi_div_two_sub] at h
  exact sub_pos.mp h

/-- Every point of every side of the candidate cell sees one of the
saved progress-body pairs under more than the certified lower angle. -/
theorem lowerVisualAngle_q100_face_one_one (i : Fin 6) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    let p := AffineMap.lineMap (q100FirstCorner i) (q100FirstCorner (i + 1)) t
    ∃ j k : Fin 48, 81.841 * π / 180 < angle (p - q100FirstBody j) (p - q100FirstBody k) := by
  have a_pos : 0 < 81.841 * π / 180 := by positivity
  have a_small : 81.841 * π / 180 ≤ π / 2 := by linarith [pi_pos]
  exact SideVisualWitness.lowerVisualAngle_of_check certificateDenominator_pos
    a_pos a_small (by norm_num) q100FirstCot_lt checkQ100FirstCot
    (checkQ100FirstCorner i) (checkQ100FirstCorner (i + 1)) checkQ100FirstBody
    (q100FirstPanels i) (q100FirstPanels_nonempty i) (q100FirstPanels_cover i)
    (q100FirstPanels_valid i) ht

end Unfoldings.FewestNets
