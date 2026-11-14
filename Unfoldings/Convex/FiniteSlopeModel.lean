module

public import Unfoldings.Convex.SlopeEnvelope
public import Unfoldings.Geometry.SpatialEnvelope
public import Unfoldings.Geometry.GraphNormalSlope

/-! Physical supported planes constructed from finite conjugate representations. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope

structure FiniteSlopeModel (E : SlopeEnvelope) where
  slopes : Finset Plane
  nonempty : slopes.Nonempty
  included : ∀ p ∈ slopes, p ∈ E.slopes
  realizes : ∀ x, E.height x = slopes.sup' nonempty (fun p => E.affine p x)

namespace FiniteSlopeModel

variable {E : SlopeEnvelope} (M : E.FiniteSlopeModel)

abbrev Face := {p : Plane // p ∈ M.slopes}

instance : Fintype M.Face := by classical exact M.slopes.fintypeCoeSort
instance : Nonempty M.Face := by obtain ⟨p, hp⟩ := M.nonempty; exact ⟨⟨p, hp⟩⟩

def plane (f : M.Face) : SpatialPlane := SpatialPlane.ofGraph (E.dual f.val) f.val

theorem height_eq (x : Plane) : SpatialEnvelope.height M.plane x = -E.height x := by
  apply le_antisymm
  · obtain ⟨p, hp, equal⟩ := Finset.exists_mem_eq_sup' M.nonempty (fun p => E.affine p x)
    have bound := AffineEnvelope.height_le (fun f => (M.plane f).height) x ⟨p, hp⟩
    rw [M.realizes, equal]
    change SpatialEnvelope.height M.plane x ≤ E.dual p - inner ℝ p x at bound
    have comm : inner ℝ p x = inner ℝ x p := real_inner_comm _ _
    dsimp [affine]
    rw [comm] at bound
    linarith
  · obtain ⟨f, equal⟩ := AffineEnvelope.exists_height_eq (fun f => (M.plane f).height) x
    change SpatialEnvelope.height M.plane x = E.dual f.val - inner ℝ f.val x at equal
    have lower := E.affine_le x (M.included f.val f.property)
    dsimp [affine] at lower
    have comm : inner ℝ f.val x = inner ℝ x f.val := real_inner_comm _ _
    rw [comm] at equal
    linarith

theorem normalSlope (f : M.Face) : (M.plane f).normalSlope = f.val :=
  SpatialPlane.ofGraph_normalSlope _ _

end FiniteSlopeModel
end Unfoldings.SlopeEnvelope
