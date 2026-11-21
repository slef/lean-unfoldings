module

public import Unfoldings.FewestNets.FiniteVisualExample

/-! Cache the kernel-verified side coordinates of the first finite record. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeshStar

/-- Reuse a proved enclosure table when the same coordinates are tested against many pairs. -/
def CheckedReal.withBounds {D : ℕ} {x : ℝ} (a : CheckedReal D x)
    (interval : FixedPointInterval D) (h : a.bounds = some interval) : CheckedReal D x where
  bounds := some interval
  sound b hb := a.sound b (h.trans hb)

def q100FirstNormal (i : Fin 6) : Plane := (face 100 1 1).physicalSideNormal i

def q100FirstOffset (i : Fin 6) : ℝ := (face 100 1 1).derivativeNormalizedSideOffset 100 i

def checkQ100FirstNormal (i : Fin 6) : CheckedPlane certificateDenominator (q100FirstNormal i) :=
  let pos := certificateDenominator_pos
  (checkFace pos 100 1 1).physicalSideNormal pos i

def checkQ100FirstOffset (i : Fin 6) : CheckedReal certificateDenominator (q100FirstOffset i) :=
  let pos := certificateDenominator_pos
  (checkFace pos 100 1 1).derivativeNormalizedSideOffset pos 100 i

/-- Kernel-computed scaled endpoints of the two coordinates and offset. -/
def q100FirstSideBounds (i : Fin 6) (j : Fin 3) :
    FixedPointInterval certificateDenominator :=
  (![
    ![
      ⟨1208925819614629174693564, 1208925819614629174708254⟩,
      ⟨-8728, 8728⟩,
      ⟨1145756504081307749810219, 1145756504081307757371013⟩
    ],
    ![
      ⟨705467170469832492517028, 705467170469832492539929⟩,
      ⟨981742180371298511404116, 981742180371298511454110⟩,
      ⟨976370150965705905751147, 976370150965705912213006⟩
    ],
    ![
      ⟨-705467170469832492540150, -705467170469832492516918⟩,
      ⟨981742180371298511403586, 981742180371298511454663⟩,
      ⟨976370150965705905751147, 976370150965705912213006⟩
    ],
    ![
      ⟨-1208925819614629174708254, -1208925819614629174693564⟩,
      ⟨-8728, 8728⟩,
      ⟨1145756504081307749810219, 1145756504081307757371013⟩
    ],
    ![
      ⟨-705467170469832492541558, -705467170469832492519162⟩,
      ⟨-981742180371298511456191, -981742180371298511407399⟩,
      ⟨987132471498170870335446, 987132471498170876868026⟩
    ],
    ![
      ⟨705467170469832492515612, 705467170469832492541776⟩,
      ⟨-981742180371298511457172, -981742180371298511401630⟩,
      ⟨987132471498170870335446, 987132471498170876872840⟩
    ]
  ] i : Fin 3 → FixedPointInterval certificateDenominator) j

set_option maxRecDepth 8192 in
theorem q100FirstNormal_bounds (i : Fin 6) (j : Fin 2) :
    (checkQ100FirstNormal i j).bounds = some (q100FirstSideBounds i j.castSucc) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 8192 in
theorem q100FirstOffset_bounds (i : Fin 6) :
    (checkQ100FirstOffset i).bounds = some (q100FirstSideBounds i 2) := by
  fin_cases i <;> decide +kernel

def checkedQ100FirstNormal (i : Fin 6) :
    CheckedPlane certificateDenominator (q100FirstNormal i) :=
  fun j => (checkQ100FirstNormal i j).withBounds (q100FirstSideBounds i j.castSucc)
    (q100FirstNormal_bounds i j)

def checkedQ100FirstOffset (i : Fin 6) :
    CheckedReal certificateDenominator (q100FirstOffset i) :=
  (checkQ100FirstOffset i).withBounds (q100FirstSideBounds i 2) (q100FirstOffset_bounds i)

end Unfoldings.FewestNets
