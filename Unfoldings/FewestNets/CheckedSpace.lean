module

public import Unfoldings.Basic
public import Unfoldings.FewestNets.CheckedReal
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Analysis.Normed.Module.Normalize

/-! Coordinatewise enclosures of exact spatial operations. -/

@[expose] public section

namespace Unfoldings.FewestNets

noncomputable section

/-- The cross product in the standard oriented Euclidean coordinates. -/
noncomputable def spatialCross (a b : Space) : Space :=
  WithLp.toLp 2 (crossProduct (WithLp.ofLp a) (WithLp.ofLp b))

/-- Check each of the three Euclidean coordinates at a common precision. -/
abbrev CheckedSpace (D : ℕ) (a : Space) := (i : Fin 3) → CheckedReal D (a i)

namespace CheckedSpace

variable {D : ℕ} {a b : Space} {s : ℝ}

/-- A checked vector assembled from its three coordinate enclosures. -/
def vec {x y z : ℝ} (a : CheckedReal D x) (b : CheckedReal D y) (c : CheckedReal D z) :
    CheckedSpace D (WithLp.toLp 2 ![x, y, z]) :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun i => Fin.elim0 i)))

/-- Addition of checked Euclidean vectors. -/
def add (x : CheckedSpace D a) (y : CheckedSpace D b) : CheckedSpace D (a + b) :=
  fun i => (x i).add (y i)

/-- Subtraction of checked Euclidean vectors. -/
def sub (x : CheckedSpace D a) (y : CheckedSpace D b) : CheckedSpace D (a - b) :=
  fun i => (x i).sub (y i)

def smul (hD : 0 < D) (c : CheckedReal D s) (x : CheckedSpace D a) :
    CheckedSpace D (s • a) :=
  fun i => c.mul hD (x i)

/-- The inner product is checked by its three-coordinate expression. -/
def dot (hD : 0 < D) (x : CheckedSpace D a) (y : CheckedSpace D b) :
    CheckedReal D (inner ℝ a b) :=
  (((x 0).mul hD (y 0)).add ((x 1).mul hD (y 1))).add ((x 2).mul hD (y 2)) |>.convert
    (by simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm, add_assoc])

def cross (hD : 0 < D) (x : CheckedSpace D a) (y : CheckedSpace D b) :
    CheckedSpace D (spatialCross a b) :=
  vec (((x 1).mul hD (y 2)).sub ((x 2).mul hD (y 1)))
    (((x 2).mul hD (y 0)).sub ((x 0).mul hD (y 2)))
    (((x 0).mul hD (y 1)).sub ((x 1).mul hD (y 0)))

def norm (hD : 0 < D) (x : CheckedSpace D a) : CheckedReal D ‖a‖ :=
  ((((x 0).square hD).add ((x 1).square hD)).add ((x 2).square hD)).sqrt hD |>.convert
    (by
      have h := congrArg Real.sqrt (EuclideanSpace.real_norm_sq_eq a)
      simpa only [Fin.sum_univ_three] using h.symm.trans (Real.sqrt_sq (norm_nonneg a)))

/-- Coordinatewise division by one real scalar. -/
def divide (hD : 0 < D) (x : CheckedSpace D a) (c : CheckedReal D s) :
    CheckedSpace D (s⁻¹ • a) :=
  fun i => ((x i).div hD c).convert (by simp [div_eq_inv_mul])

def normalize (hD : 0 < D) (x : CheckedSpace D a) :
    CheckedSpace D (NormedSpace.normalize a) :=
  divide hD x (norm hD x)

end CheckedSpace
end

end Unfoldings.FewestNets
