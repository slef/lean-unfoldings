module

public import Unfoldings.FewestNets.MeshStar

/-! Fixed-point checking of the exact icosahedral site-star coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.MeshStar

open CheckedReal CheckedSpace

/-- Enclosures of a site and all its cyclic neighbors. -/
structure Checked (D : ℕ) {n : ℕ} (star : MeshStar n) where
  site : CheckedSpace D star.site
  neighbor : (i : Fin n) → CheckedSpace D (star.neighbor i)

variable {D : ℕ} (hD : 0 < D)

def checkNat (D : ℕ) (n : ℕ) : CheckedReal D (n : ℝ) :=
  (rat D (n : ℚ)).convert (by simp)

def checkHeightSq : CheckedReal D faceHeightSq :=
  ((rat D 5).add ((rat D 2).mul hD ((rat D 5).sqrt hD))).div hD (rat D 15) |>.convert
    (by simp [faceHeightSq])

def checkHeight : CheckedReal D faceHeight := (checkHeightSq hD).sqrt hD

def checkScale : CheckedReal D faceScale :=
  (((rat D 1).sub (checkHeightSq hD)).div hD (rat D 4)).sqrt hD |>.convert
    (by simp [faceScale])

def checkA : CheckedSpace D cornerA :=
  let s := checkScale hD
  vec (((rat D 3).sqrt hD).mul hD s |>.neg |>.convert (by simp)) s.neg (checkHeight hD)

def checkB : CheckedSpace D cornerB :=
  let s := checkScale hD
  vec (((rat D 3).sqrt hD).mul hD s |>.convert (by simp)) s.neg (checkHeight hD)

def checkC : CheckedSpace D cornerC :=
  vec ((rat D 0).convert (by simp)) (((rat D 2).mul hD (checkScale hD)).convert (by simp))
    (checkHeight hD)

def checkU (q : ℕ) : CheckedSpace D (stepU q) :=
  divide hD (sub (checkB hD) (checkA hD)) (checkNat D q)

def checkV (q : ℕ) : CheckedSpace D (stepV q) :=
  divide hD (sub (checkC hD) (checkA hD)) (checkNat D q)

def checkFaceOffset (q : ℕ) (k : Fin 6) : CheckedSpace D (faceOffset q k) := by
  let u := checkU hD q
  let v := checkV hD q
  let n : CheckedReal D (-1 : ℝ) := (rat D (-1)).convert (by simp)
  exact Fin.cases (motive := fun k => CheckedSpace D (faceOffset q k)) u
    (Fin.cases v (Fin.cases (sub v u) (Fin.cases (smul hD n u)
      (Fin.cases (smul hD n v) (Fin.cases (sub u v) (fun i => Fin.elim0 i)))))) k

def checkFace (q i j : ℕ) : Checked D (face q i j) :=
  let iq := (checkNat D i).div hD (checkNat D q)
  let jq := (checkNat D j).div hD (checkNat D q)
  let a := checkA hD
  let b := checkB hD
  let c := checkC hD
  let z := add (add c (smul hD iq (sub b c))) (smul hD jq (sub a c))
  ⟨z, fun k => add z (checkFaceOffset hD q k)⟩

def checkReflection {x : Space} (cx : CheckedSpace D x) : CheckedSpace D (reflectAB x) :=
  let r := CheckedSpace.normalize hD (cross hD (checkA hD) (checkB hD))
  let two : CheckedReal D (2 : ℝ) := (rat D 2).convert (by simp)
  sub cx (smul hD (two.mul hD (dot hD cx r)) r)

def checkSeamNeighbor (q : ℕ) {z : Space} (cz : CheckedSpace D z) (k : Fin 6) :
    CheckedSpace D (seamNeighbor q z k) := by
  let u := checkU hD q
  let v := checkV hD q
  exact Fin.cases (motive := fun k => CheckedSpace D (seamNeighbor q z k)) (add cz u)
    (Fin.cases (add cz v) (Fin.cases (add cz (sub v u)) (Fin.cases (sub cz u)
      (Fin.cases (checkReflection hD (add cz (sub v u)))
        (Fin.cases (checkReflection hD (add cz v)) (fun i => Fin.elim0 i)))))) k

def checkSeam (q i : ℕ) : Checked D (seam q i) :=
  let z := add (checkA hD) (smul hD (checkNat D i) (checkU hD q))
  ⟨z, checkSeamNeighbor hD q z⟩

def checkFifthTurn {x : Space} (cx : CheckedSpace D x) : CheckedSpace D (fifthTurn x) :=
  let r := CheckedSpace.normalize hD (checkA hD)
  let one : CheckedReal D (1 : ℝ) := (rat D 1).convert (by simp)
  let four : CheckedReal D (4 : ℝ) := (rat D 4).convert (by simp)
  let sq5 : CheckedReal D (Real.sqrt 5) := ((rat D 5).sqrt hD).convert (by simp)
  let c := (sq5.sub one).div hD four
  let s := (one.sub (c.square hD)).sqrt hD
  add (add (smul hD c cx) (smul hD s (cross hD r cx)))
    (smul hD ((one.sub c).mul hD (dot hD r cx)) r)

def checkFifthIterate {x : Space} (cx : CheckedSpace D x) (k : ℕ) :
    CheckedSpace D (fifthTurn^[k] x) :=
  match k with
  | 0 => cx
  | k + 1 => fun i => ((checkFifthTurn hD (checkFifthIterate cx k)) i).convert
      (by rw [Function.iterate_succ_apply'])

def checkPentagon (q : ℕ) : Checked D (pentagon q) :=
  ⟨checkA hD, fun k => checkFifthIterate hD (add (checkA hD) (checkU hD q)) k.val⟩

namespace Checked

variable {n : ℕ} {star : MeshStar (n + 1)} (a : Checked D star)

def direction : CheckedSpace D star.direction := CheckedSpace.normalize hD a.site

def neighborDirection (i : Fin (n + 1)) : CheckedSpace D (star.neighborDirection i) :=
  CheckedSpace.normalize hD (a.neighbor i)

def dual (i : Fin (n + 1)) : CheckedSpace D (star.dual i) :=
  cross hD (sub (a.neighborDirection hD i) (a.direction hD))
    (sub (a.neighborDirection hD (i + 1)) (a.direction hD))

def dualDirection (i : Fin (n + 1)) : CheckedSpace D (star.dualDirection i) :=
  CheckedSpace.normalize hD (a.dual hD i)

def dualOffset (i : Fin (n + 1)) :
    CheckedReal D (inner ℝ star.direction (star.dual i)) :=
  dot hD (a.direction hD) (a.dual hD i)

def gnomonicVertex (i : Fin (n + 1)) : CheckedSpace D (star.gnomonicVertex i) :=
  sub (divide hD (a.dual hD i) (a.dualOffset hD i)) (a.direction hD)

end Checked
end Unfoldings.FewestNets.MeshStar
