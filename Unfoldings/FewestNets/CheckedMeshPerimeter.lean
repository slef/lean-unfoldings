module

public import Unfoldings.FewestNets.MeshArcLength
public import Unfoldings.FewestNets.FiniteMeshKeys
public import Mathlib.Data.List.FinRange

/-! Sum the canonical stars' dual side enclosures with their orbit multiplicities. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open scoped BigOperators

namespace CheckedReal

/-- Accumulate a list of exact expressions with outward-rounded addition. -/
def sumList {D : ℕ} {I : Type*} (f : I → ℝ) (checked : ∀ i, CheckedReal D (f i))
    (keys : List I) : CheckedReal D (keys.map f).sum :=
  match keys with
  | [] => (rat D 0).convert (by simp)
  | i :: more => (checked i).add (sumList f checked more)

end CheckedReal

namespace MeshStar

open InnerProductGeometry

variable {n : ℕ} (star : MeshStar (n + 1))

def arcUpperPerimeter : ℝ := ∑ i, star.dualArcUpper i

theorem perimeter_le_arcUpperPerimeter
    (outward : ∀ i, 0 < inner ℝ star.direction (star.dual i)) :
    (∑ i, angle (star.dualDirection i) (star.dualDirection (i + 1))) ≤ star.arcUpperPerimeter :=
  Finset.sum_le_sum fun i _ => dualAngle_le_dualArcUpper (star := star) i outward

namespace Checked

variable {star}

def arcUpperPerimeter {D : ℕ} (hD : 0 < D) (a : Checked D star) :
    CheckedReal D star.arcUpperPerimeter :=
  (CheckedReal.sumList star.dualArcUpper (a.dualArcUpper hD) (List.finRange (n + 1))).convert
    (by rw [← List.ofFn_eq_map, List.sum_ofFn, MeshStar.arcUpperPerimeter])

end Checked
end MeshStar

open MeshStar CheckedReal

def faceWeightedPerimeter (q : ℕ) (key : ℕ × ℕ) : ℝ :=
  (faceMeshKeyWeight q key.1 key.2 : ℝ) * (face q key.1 key.2).arcUpperPerimeter

def seamWeightedPerimeter (q : ℕ) (key : ℕ) : ℝ :=
  (seamMeshKeyWeight q key : ℝ) * (seam q key).arcUpperPerimeter

def checkFacePerimeter {D : ℕ} (hD : 0 < D) (q : ℕ) (key : ℕ × ℕ) :
    CheckedReal D (faceWeightedPerimeter q key) :=
  (checkNat D (faceMeshKeyWeight q key.1 key.2)).mul hD
    ((checkFace hD q key.1 key.2).arcUpperPerimeter hD)

def checkSeamPerimeter {D : ℕ} (hD : 0 < D) (q key : ℕ) :
    CheckedReal D (seamWeightedPerimeter q key) :=
  (checkNat D (seamMeshKeyWeight q key)).mul hD ((checkSeam hD q key).arcUpperPerimeter hD)

/-- The candidate network length counts each dual side in both site perimeters. -/
def weightedArcUpperTotal (q : ℕ) : ℝ :=
  (20 * ((faceMeshKeys q).map (faceWeightedPerimeter q)).sum +
    30 * ((seamMeshKeys q).map (seamWeightedPerimeter q)).sum +
    12 * (pentagon q).arcUpperPerimeter) / 2

def faceMeshKeyBlock (q size block : ℕ) : List (ℕ × ℕ) :=
  ((faceMeshKeys q).drop (size * block)).take size

def seamMeshKeyBlock (q size block : ℕ) : List ℕ :=
  ((seamMeshKeys q).drop (size * block)).take size

def checkFaceBlockPerimeter {D : ℕ} (hD : 0 < D) (q size block : ℕ) :
    CheckedReal D (((faceMeshKeyBlock q size block).map (faceWeightedPerimeter q)).sum) :=
  sumList (faceWeightedPerimeter q) (checkFacePerimeter hD q) (faceMeshKeyBlock q size block)

def checkSeamBlockPerimeter {D : ℕ} (hD : 0 < D) (q size block : ℕ) :
    CheckedReal D (((seamMeshKeyBlock q size block).map (seamWeightedPerimeter q)).sum) :=
  sumList (seamWeightedPerimeter q) (checkSeamPerimeter hD q) (seamMeshKeyBlock q size block)

end Unfoldings.FewestNets
