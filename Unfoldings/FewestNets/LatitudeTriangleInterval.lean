module

public import Unfoldings.FewestNets.LatitudeChargeIntervals
public import Unfoldings.FewestNets.LatitudeSphericalMetrics

/-! Evaluate a latitude triangle with an independently enclosed band height. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real CheckedReal

local notation "D" => countPrecision
local notation "hD" => countPrecision_pos
local notation "Q" => CheckedReal.rat countPrecision

abbrev CheckedCount (x : ℝ) := CheckedReal countPrecision x

/-- The exact squared chords in base, right, left order. Reverse the last
two when the upper row is the base. -/
def latitudeChordSquares (base apex step half offset : ℝ) (reversed : Bool) : Fin 3 → ℝ :=
  let b := 4 * (sin base * sin half) ^ 2
  let gap := 4 * sin (step / 2) ^ 2
  let extent := 4 * sin base * sin apex
  let right := gap + extent * sin ((offset - half) / 2) ^ 2
  let left := gap + extent * sin ((offset + half) / 2) ^ 2
  if reversed then ![b, left, right] else ![b, right, left]

/-- Signed area with the lower-longitude base vertex first. -/
def latitudeDetValue (base apex step half offset : ℝ) : ℝ :=
  2 * sin base * sin half *
    (-sin step + cos base * sin apex * (1 - cos offset) - sin base * cos apex * (1 - cos half))

def checkLatitudeDet {base apex step half offset : ℝ}
    (sb : CheckedCount (sin base)) (cb : CheckedCount (cos base))
    (sa : CheckedCount (sin apex)) (ca : CheckedCount (cos apex))
    (sd : CheckedCount (sin step)) (sh : CheckedCount (sin half))
    (h : CheckedCount half) (t : CheckedCount offset) : CheckedCount (latitudeDetValue base apex step half offset) := by
  let bend := (Q 1).sub (h.checkCosCentered hD 10)
  let apexBend := (Q 1).sub (t.checkCosCentered hD 10)
  let outer := ((Q 2).mul hD sb).mul hD sh
  let correction₁ := (cb.mul hD sa).mul hD apexBend
  let correction₂ := (sb.mul hD ca).mul hD bend
  exact (outer.mul hD ((sd.neg.add correction₁).sub correction₂)).convert (by
    unfold latitudeDetValue
    norm_num)

def checkLatitudeChordSquares {base apex step half offset : ℝ}
    (sb : CheckedCount (sin base)) (sa : CheckedCount (sin apex)) (sh : CheckedCount (sin half))
    (ds : CheckedCount (sin (step / 2)))
    (h : CheckedCount half) (t : CheckedCount offset) (reversed : Bool) (i : Fin 3) :
    CheckedCount (latitudeChordSquares base apex step half offset reversed i) := by
  let l := ((t.add h).div hD (Q 2)).checkSinCentered hD 10
  let r := ((t.sub h).div hD (Q 2)).checkSinCentered hD 10
  let S := (Q 4).mul hD ((sb.mul hD sh).square hD)
  let gap := (Q 4).mul hD (ds.square hD)
  let extent := ((Q 4).mul hD sb).mul hD sa
  let L := gap.add (extent.mul hD (l.square hD))
  let R := gap.add (extent.mul hD (r.square hD))
  if h₀ : i = 0 then
    exact S.convert (by subst i; cases reversed <;> norm_num [latitudeChordSquares])
  else if h₁ : i = 1 then
    exact if hr : reversed = true then
      L.convert (by simp [latitudeChordSquares, h₁, hr])
    else
      R.convert (by simp [latitudeChordSquares, h₁, hr])
  else
    have h₂ : i = 2 := by
      apply Fin.ext
      have l := i.isLt
      have u : i.val ≠ 0 := fun h => h₀ (Fin.ext h)
      have v : i.val ≠ 1 := fun h => h₁ (Fin.ext h)
      change i.val = 2
      omega
    exact if hr : reversed = true then
      R.convert (by simp [latitudeChordSquares, h₂, hr])
    else
      L.convert (by simp [latitudeChordSquares, h₂, hr])

def latitudeSineSquares (base apex step half offset : ℝ) (reversed : Bool) (i : Fin 3) : ℝ :=
  let d := max 0 (latitudeChordSquares base apex step half offset reversed i)
  d * (1 - d / 4)

/-- Real charge formula corresponding to the executable input data. -/
def latitudeTriangleCharge (base apex step half offset : ℝ) (reversed : Bool) : ℝ :=
  let s := latitudeSineSquares base apex step half offset reversed
  max ((2 / π) * shortSideRatio (max (s 0) (max (s 1) (s 2))) *
      ((∑ j : Fin 3, √(s j * s (j + 2))) / |latitudeDetValue base apex step half offset|))
    ((∑ j : Fin 3, √(s j) * shortSideRatio (s j)) / (π * 0.115))

def checkLatitudeTriangleOfTrig {base apex step half offset : ℝ}
    (sb : CheckedCount (sin base)) (cb : CheckedCount (cos base))
    (sa : CheckedCount (sin apex)) (ca : CheckedCount (cos apex))
    (sd : CheckedCount (sin step)) (ds : CheckedCount (sin (step / 2)))
    (h : CheckedCount half) (t : CheckedCount offset) (reversed : Bool) :
    CheckedCount (latitudeTriangleCharge base apex step half offset reversed) :=
  (h.checkSinCentered hD 10).reuse fun sh =>
    h.reuse fun h' =>
    t.reuse fun t' =>
    checkTriangleCharge (fun j => checkChordSineSquared
      (((Q 0).convert (by norm_num)).maximum hD (checkLatitudeChordSquares sb sa sh ds h' t' reversed j))
      (le_max_left _ _)) (checkLatitudeDet sb cb sa ca sd sh h' t')

def checkLatitudeTriangle {base apex step half offset : ℝ}
    (b : CheckedCount base) (a : CheckedCount apex) (d : CheckedCount step)
    (h : CheckedCount half) (t : CheckedCount offset) (reversed : Bool) :
    CheckedCount (latitudeTriangleCharge base apex step half offset reversed) :=
  (b.checkSinCentered hD 24).reuse fun sb =>
  (b.checkCosCentered hD 24).reuse fun cb =>
  (a.checkSinCentered hD 24).reuse fun sa =>
  (a.checkCosCentered hD 24).reuse fun ca =>
  (d.checkSinCentered hD 10).reuse fun sd =>
  ((d.div hD (Q 2)).checkSinCentered hD 10).reuse fun ds =>
  checkLatitudeTriangleOfTrig sb cb sa ca sd ds h t reversed

end Unfoldings.FewestNets.RevisedLatitudeGrid
