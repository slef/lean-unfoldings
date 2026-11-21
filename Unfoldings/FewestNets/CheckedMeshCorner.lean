module

public import Unfoldings.FewestNets.MeshCornerGeometry
public import Unfoldings.FewestNets.CheckedMeshStar
public import Unfoldings.FewestNets.CheckedTrigonometry

/-! Exact fixed-point checks of a centered corner's altitude and incident angle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry Real

/-- The distance from the origin to the line through the two gnomonic endpoints. -/
def meshCornerAltitude (p q : Space) : ℝ := ‖spatialCross p q‖ / ‖q - p‖

/-- The normalized dot product of the two gnomonic rays. -/
def meshCornerCosine (p q : Space) : ℝ := inner ℝ p q / (‖p‖ * ‖q‖)

theorem meshCornerCosine_eq_cos_angle {p q : Space} (hp : p ≠ 0) (hq : q ≠ 0) :
    meshCornerCosine p q = cos (angle p q) := by
  rw [meshCornerCosine, ← cos_angle_mul_norm_mul_norm, mul_div_cancel_right₀ _ (by positivity)]

theorem angle_gt_of_meshCornerCosine_lt {p q : Space} (hp : p ≠ 0) (hq : q ≠ 0)
    {ψ : ℝ} (low : 0 ≤ ψ) (high : ψ ≤ π) (h : meshCornerCosine p q < cos ψ) :
    ψ < angle p q := by
  rw [meshCornerCosine_eq_cos_angle hp hq] at h
  by_contra! other
  exact (not_lt_of_ge (Real.strictAntiOn_cos.antitoneOn
    ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ⟨low, high⟩ other)) h

namespace CheckedSpace

variable {D : ℕ} {p q : Space} (hD : 0 < D)

def meshGnomonic {u v : Space} (cu : CheckedSpace D u) (cv : CheckedSpace D v) :
    CheckedSpace D (FewestNets.meshGnomonic u v) :=
  sub (divide hD cv (dot hD cu cv)) cu

def meshCornerAltitude (cp : CheckedSpace D p) (cq : CheckedSpace D q) :
    CheckedReal D (FewestNets.meshCornerAltitude p q) :=
  (norm hD (cross hD cp cq)).div hD (norm hD (sub cq cp))

def meshCornerCosine (cp : CheckedSpace D p) (cq : CheckedSpace D q) :
    CheckedReal D (FewestNets.meshCornerCosine p q) :=
  (dot hD cp cq).div hD ((norm hD cp).mul hD (norm hD cq))

end CheckedSpace

namespace MeshStar

variable {n : ℕ} (star : MeshStar (n + 1))

/-- The ray from the `k`th dual vertex to the `j`th, in the chart about `k`. -/
def cornerRay (k j : Fin (n + 1)) : Space :=
  meshGnomonic (star.dualDirection k) (star.dualDirection j)

namespace Checked

variable {D : ℕ} (hD : 0 < D) {star} (a : Checked D star)

def cornerRay (k j : Fin (n + 1)) : CheckedSpace D (star.cornerRay k j) :=
  CheckedSpace.meshGnomonic hD (a.dualDirection hD k) (a.dualDirection hD j)

/-- The two scalar checks for the corner between the preceding and following sides. -/
def checkCorner {r ψ : ℝ} (cr : CheckedReal D (tan r)) (cψ : CheckedReal D (cos ψ))
    (k : Fin (n + 1)) : Bool :=
  let p := a.cornerRay hD k (k - 1)
  let q := a.cornerRay hD k (k + 1)
  cr.isLT (CheckedSpace.meshCornerAltitude hD p q) &&
    (CheckedSpace.meshCornerCosine hD p q).isLT cψ

theorem corner_bounds_of_check {r ψ : ℝ} (cr : CheckedReal D (tan r))
    (cψ : CheckedReal D (cos ψ)) (k : Fin (n + 1))
    (valid : a.checkCorner hD cr cψ k = true) :
    tan r < meshCornerAltitude (star.cornerRay k (k - 1)) (star.cornerRay k (k + 1)) ∧
      meshCornerCosine (star.cornerRay k (k - 1)) (star.cornerRay k (k + 1)) < cos ψ := by
  rw [checkCorner, Bool.and_eq_true] at valid
  exact ⟨CheckedReal.lt_of_isLT hD _ _ valid.1,
    CheckedReal.lt_of_isLT hD _ _ valid.2⟩

end Checked
end MeshStar

end Unfoldings.FewestNets
