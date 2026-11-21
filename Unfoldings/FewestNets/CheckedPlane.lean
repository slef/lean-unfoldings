module

public import Unfoldings.FewestNets.CheckedSpace

/-! Fixed-point enclosures in the tangent-plane coordinates of the certificate. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

/-- Each planar Euclidean coordinate carries its own proved enclosure. -/
abbrev CheckedPlane (D : ℕ) (p : Plane) := (i : Fin 2) → CheckedReal D (p i)

namespace CheckedPlane

variable {D : ℕ} {a b : Plane} {s : ℝ}

def vec {x y : ℝ} (a : CheckedReal D x) (b : CheckedReal D y) :
    CheckedPlane D (WithLp.toLp 2 ![x, y]) :=
  Fin.cases a (Fin.cases b (fun i => Fin.elim0 i))

def rat (D : ℕ) (x y : ℚ) : CheckedPlane D (WithLp.toLp 2 ![(x : ℝ), (y : ℝ)]) :=
  vec (CheckedReal.rat D x) (CheckedReal.rat D y)

def add (a' : CheckedPlane D a) (b' : CheckedPlane D b) : CheckedPlane D (a + b) :=
  fun i => (a' i).add (b' i)

def sub (a' : CheckedPlane D a) (b' : CheckedPlane D b) : CheckedPlane D (a - b) :=
  fun i => (a' i).sub (b' i)

def smul (hD : 0 < D) (cs : CheckedReal D s) (a' : CheckedPlane D a) :
    CheckedPlane D (s • a) :=
  fun i => cs.mul hD (a' i)

def divide (hD : 0 < D) (a' : CheckedPlane D a) (r : CheckedReal D s) :
    CheckedPlane D (s⁻¹ • a) :=
  fun i => ((a' i).div hD r).convert (by simp [div_eq_inv_mul])

def dot (hD : 0 < D) (a' : CheckedPlane D a) (b' : CheckedPlane D b) :
    CheckedReal D (inner ℝ a b) :=
  (((a' 0).mul hD (b' 0)).add ((a' 1).mul hD (b' 1))).convert
    (by simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm])

def det (hD : 0 < D) (a' : CheckedPlane D a) (b' : CheckedPlane D b) :
    CheckedReal D (a 0 * b 1 - a 1 * b 0) :=
  ((a' 0).mul hD (b' 1)).sub ((a' 1).mul hD (b' 0))

def normSq (hD : 0 < D) (a' : CheckedPlane D a) : CheckedReal D (‖a‖ ^ 2) :=
  (((a' 0).square hD).add ((a' 1).square hD)).convert
    (by rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two])

def norm (hD : 0 < D) (a' : CheckedPlane D a) : CheckedReal D ‖a‖ :=
  ((normSq hD a').sqrt hD).convert (Real.sqrt_sq (norm_nonneg a))

end CheckedPlane
end Unfoldings.FewestNets
