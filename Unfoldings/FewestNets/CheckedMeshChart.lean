module

public import Unfoldings.FewestNets.CheckedMeshStar
public import Unfoldings.FewestNets.MeshChartFrame
public import Unfoldings.FewestNets.CheckedPlane

/-! Enclose the actual finite gnomonic coordinates and their derivative rescaling. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.MeshStar

variable {n : ℕ} (star : MeshStar (n + 1))

def derivativeNormalizedVertex (q : ℕ) (i : Fin (n + 1)) : Plane :=
  (star.derivativeRadius q)⁻¹ • star.physicalVertex i

def derivativeNormalizedSideOffset (q : ℕ) (i : Fin (n + 1)) : ℝ :=
  star.physicalSideOffset i / star.derivativeRadius q

namespace Checked

open CheckedReal

variable {D : ℕ} (hD : 0 < D)

def bisectorTangent {s t : Space} (cs : CheckedSpace D s) (ct : CheckedSpace D t) :
    CheckedSpace D (FewestNets.bisectorTangent s t) :=
  CheckedSpace.sub ct (CheckedSpace.smul hD (CheckedSpace.dot hD cs ct) cs)

def chartFirst {s : Space} (cs : CheckedSpace D s) : CheckedSpace D (MeshStar.chartFirst s) :=
  let one : CheckedReal D (1 : ℝ) := (rat D 1).convert (by simp)
  let zero : CheckedReal D (0 : ℝ) := (rat D 0).convert (by simp)
  let ex := CheckedSpace.vec one zero zero
  CheckedSpace.normalize hD (bisectorTangent hD cs ex)

def chartSecond {s : Space} (cs : CheckedSpace D s) : CheckedSpace D (MeshStar.chartSecond s) :=
  CheckedSpace.cross hD cs (chartFirst hD cs)

def chartPoint {s z : Space} (cs : CheckedSpace D s) (cz : CheckedSpace D z) :
    CheckedPlane D (MeshStar.chartPoint s z) :=
  CheckedPlane.vec (CheckedSpace.dot hD cz (chartFirst hD cs))
    (CheckedSpace.dot hD cz (chartSecond hD cs))

variable {star} (a : Checked D star)

def physicalVertex (i : Fin (n + 1)) : CheckedPlane D (star.physicalVertex i) :=
  chartPoint hD (a.direction hD) (a.gnomonicVertex hD i)

def physicalSideNormal (i : Fin (n + 1)) : CheckedPlane D (star.physicalSideNormal i) :=
  let s := a.direction hD
  let t := a.neighborDirection hD i
  chartPoint hD s (CheckedSpace.normalize hD (bisectorTangent hD s t))

def physicalSideOffset (i : Fin (n + 1)) : CheckedReal D (star.physicalSideOffset i) :=
  let s := a.direction hD
  let t := a.neighborDirection hD i
  let one : CheckedReal D (1 : ℝ) := (rat D 1).convert (by simp)
  (CheckedSpace.norm hD (bisectorTangent hD s t)).div hD (one.add (CheckedSpace.dot hD s t))

def relativeDirection {w : Space} (cw : CheckedSpace D w) :
    CheckedPlane D (star.relativeDirection w) :=
  let s := a.direction hD
  chartPoint hD s (CheckedSpace.divide hD (bisectorTangent hD s cw) (CheckedSpace.norm hD a.site))

def derivativeRadius (q : ℕ) : CheckedReal D (star.derivativeRadius q) :=
  let u := a.relativeDirection hD (checkU hD q)
  let v := a.relativeDirection hD (checkV hD q)
  let two : CheckedReal D (2 : ℝ) := (rat D 2).convert (by simp)
  let aa := (CheckedPlane.normSq hD u).div hD two
  let bb := (CheckedPlane.normSq hD v).div hD two
  let c := CheckedPlane.det hD u v
  let x := ((aa.mul hD (v 1)).sub ((u 1).mul hD bb)).div hD c
  let y := (((u 0).mul hD bb).sub (aa.mul hD (v 0))).div hD c
  CheckedPlane.norm hD (CheckedPlane.vec x y)

def derivativeNormalizedVertex (q : ℕ) (i : Fin (n + 1)) :
    CheckedPlane D (star.derivativeNormalizedVertex q i) :=
  CheckedPlane.divide hD (a.physicalVertex hD i) (a.derivativeRadius hD q)

def derivativeNormalizedSideOffset (q : ℕ) (i : Fin (n + 1)) :
    CheckedReal D (star.derivativeNormalizedSideOffset q i) :=
  (a.physicalSideOffset hD i).div hD (a.derivativeRadius hD q)

end Checked
end Unfoldings.FewestNets.MeshStar
