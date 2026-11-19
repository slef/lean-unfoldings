module

public import Unfoldings.Geometry.OrientedBankGap
public import Unfoldings.Geometry.BankGapParameters
public import Unfoldings.Geometry.PolygonalRayTransfer
public import Unfoldings.Geometry.SourceOpeningBankGap

/-! Collapse a rigid source gap along each circle to the original first bank. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (B : PolygonalRay ℂ n)

/-- The source-fixed rotation takes every literal finite edge or infinite tail parameter
to the same parameter of the rotated bank. -/
theorem rotateSuffix_zero_addressPoint (θ : ℝ) (a : Address n) :
    (B.rotateSuffix 0 θ).addressPoint a = sourceRotation B.start θ (B.addressPoint a) := by
  rw [B.rotateSuffix_zero_eq_affineMap]
  cases a with
  | inl p => exact B.chain.affineMap_point _ p.1 p.2
  | inr t => exact B.affineMap_tail _ t

/-- Radius is unchanged at every original parameter, including the whole tail. -/
theorem rotateSuffix_zero_addressPoint_nndist (θ : ℝ) (a : Address n) :
    nndist B.start ((B.rotateSuffix 0 θ).addressPoint a) =
      nndist B.start (B.addressPoint a) := by
  rw [B.rotateSuffix_zero_addressPoint]
  have fixed : sourceRotation B.start θ B.start = B.start := by
    rw [sourceRotation_apply, sub_self, map_zero, add_zero]
  calc
    _ = nndist (sourceRotation B.start θ B.start)
        (sourceRotation B.start θ (B.addressPoint a)) :=
      congrArg (fun v => nndist v (sourceRotation B.start θ (B.addressPoint a))) fixed.symm
    _ = _ := (sourceRotation B.start θ).isometry.nndist_eq _ _

end Unfoldings.PolygonalRay

namespace Unfoldings.OrientedBankGap

variable {n : ℕ} {B : PolygonalRay ℂ n} {θ : ℝ} (G : OrientedBankGap B (B.rotateSuffix 0 θ))

/-- The radial projection is continuous in the entire original gap metric. It retains
both source-fixed banks' arclength addresses on the original first bank. -/
def projectFirstBank (x : PolygonalPoint G.model.region) : B.carrier :=
  (B.radialHomeomorph G.first_outward G.first_nonzero).symm (nndist B.start x.val)

theorem continuous_projectFirstBank : Continuous G.projectFirstBank :=
  (B.radialHomeomorph G.first_outward G.first_nonzero).symm.continuous.comp
    (continuous_const.nndist (continuous_subtype_val.comp PolygonalPoint.continuous_toSubtype))

/-- Bounded pieces of the rolled first bank have compact inverse image in the gap. -/
theorem isProperMap_projectFirstBank : IsProperMap G.projectFirstBank :=
  (B.radialHomeomorph G.first_outward G.first_nonzero).symm.isProperMap.comp
    ((isProperMap_nndist B.start).comp (G.model.closed.isClosedEmbedding_subtypeVal.isProperMap.comp
      (B.twoBankGapIntrinsicHomeomorph (B.rotateSuffix 0 θ) G.first_outward G.first_nonzero
        G.second_outward G.second_nonzero G.phase G.common).isProperMap))

@[simp] theorem projectFirstBank_edgePoint (side : Bool) (i : Fin n) (t : unitInterval) :
    G.projectFirstBank (G.model.edgePoint side i t) =
      ⟨B.addressPoint (.inl (i, t)), B.addressPoint_mem (.inl (i, t))⟩ := by
  apply (B.radialHomeomorph G.first_outward G.first_nonzero).injective
  rw [projectFirstBank, Homeomorph.apply_symm_apply]
  cases side
  · rfl
  · exact B.rotateSuffix_zero_addressPoint_nndist θ (.inl (i, t))

@[simp] theorem projectFirstBank_tailPoint (side : Bool) (t : ℝ≥0) :
    G.projectFirstBank (G.model.tailPoint side t) =
      ⟨B.addressPoint (.inr t), B.addressPoint_mem (.inr t)⟩ := by
  apply (B.radialHomeomorph G.first_outward G.first_nonzero).injective
  rw [projectFirstBank, Homeomorph.apply_symm_apply]
  cases side
  · rfl
  · exact B.rotateSuffix_zero_addressPoint_nndist θ (.inr t)

end Unfoldings.OrientedBankGap
