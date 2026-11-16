module

public import Unfoldings.Geometry.SpatialEnvelope

/-! A horizontal roof section has canonical proper polygonal-window equations. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope

variable {I : Type*} [Fintype I] [Nonempty I] (family : I → SpatialPlane) (Z : ℝ)

/-- The actual supporting planes give the polygonal sides of a horizontal section. -/
def levelEquation (i : I) : Plane →ᵃ[ℝ] ℝ := (family i).height - AffineMap.const ℝ Plane Z

theorem levelEquation_domain : {p | ∀ i, 0 ≤ levelEquation family Z i p} = clip family Z := by
  ext p
  constructor
  · intro member
    obtain ⟨i, active⟩ := AffineEnvelope.exists_height_eq (fun i => (family i).height) p
    have bound := member i
    change 0 ≤ (family i).height p - Z at bound
    change Z ≤ height family p
    exact (sub_nonneg.mp bound).trans_eq active.symm
  · intro member i
    change 0 ≤ (family i).height p - Z
    exact sub_nonneg.mpr (member.trans (AffineEnvelope.height_le _ p i))

include family in
/-- A strict interior section point makes every window equation proper. -/
theorem levelEquation_ne_zero {q : Plane} (higher : Z < height family q) (i : I) :
    levelEquation family Z i ≠ 0 := by
  intro zero
  have equal := congrArg (fun f : Plane →ᵃ[ℝ] ℝ => f q) zero
  change (family i).height q - Z = 0 at equal
  have bound := AffineEnvelope.height_le (fun i => (family i).height) q i
  change height family q ≤ (family i).height q at bound
  linarith

theorem levelEquation_full {q : Plane} (higher : Z < height family q) :
    (interior {p | ∀ i, 0 ≤ levelEquation family Z i p}).Nonempty := by
  rw [levelEquation_domain]
  exact ⟨q, AffineEnvelope.mem_interior_clip (fun i => (family i).height) higher⟩

theorem levelEquation_positive {p : Plane} (higher : Z < height family p) :
    ∀ i, 0 < levelEquation family Z i p := by
  intro i
  change 0 < (family i).height p - Z
  exact sub_pos.mpr (higher.trans_le (AffineEnvelope.height_le _ p i))

end Unfoldings.SpatialEnvelope
