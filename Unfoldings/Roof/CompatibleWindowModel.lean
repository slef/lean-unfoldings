module

public import Unfoldings.Roof.CompatibleCutPartitionIndependence
public import Unfoldings.Geometry.SpatialEnvelopeWindowCut

/-! Construct actual retained whole-roof models aligned to an independent polygonal window. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β) (M : G.FiniteSlopeModel)
  {J : Type} (equations : J → Plane →ᵃ[ℝ] ℝ)

/-- One actual retained cut model, also aligned to the polygonal window's original sides. -/
structure WindowModel where
  whole : R.WholeCutModel M
  signs : whole.Index → J → Bool
  aligned : ∀ c z, z ∈ whole.partition.footprint c → ∀ j,
    0 ≤ AffineArrangement.signed (equations j) (signs c j) z

variable [Finite J]

/-- Align the original whole forest cut and all window lines in one actual finite partition. -/
def windowModel (proper : ∀ j, equations j ≠ 0) : R.WindowModel M equations :=
  Classical.choice (by
    let extra := Sum.elim R.wholeCutEquation equations
    have extra_proper : ∀ i, extra i ≠ 0 := by
      intro i
      cases i with
      | inl i => exact R.wholeCutEquation_ne_zero i
      | inr j => exact proper j
    obtain ⟨A, finite, P, signs, aligned⟩ := SpatialEnvelope.exists_wholePartition M.plane
      extra extra_proper
    let W : R.WholeCutModel M := ⟨A, finite, P, (fun c i => signs c (.inl i)),
      (fun c z hz i => aligned c z hz (.inl i))⟩
    exact ⟨⟨W, (fun c j => signs c (.inr j)), (fun c z hz j => aligned c z hz (.inr j))⟩⟩)

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
