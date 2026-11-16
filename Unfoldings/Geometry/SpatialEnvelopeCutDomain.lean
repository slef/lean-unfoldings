module

public import Unfoldings.Roof.SpatialEnvelopeCap

/-! Every original retained triangle copy projects into its actual finite roof section. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane} {Z : ℝ}
  (T : Triangulation family Z)

local instance cutDomainIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

theorem fold_horizontal_mem_clip (retain : Set T.pairedComplex.Seam)
    (x : T.pairedComplex.Realization retain) :
    Cap.horizontal (T.pairedFolding.toSpace retain x) ∈ clip family Z := by
  obtain ⟨⟨i, p⟩, rfl⟩ := MetricGluing.point_surjective T.pairedComplex.Cell
    (T.pairedComplex.glue retain) x
  exact Eq.mpr (congrArg (fun z : Plane => z ∈ clip family Z)
    ((family (T.support i)).horizontal_place p.val))
    (T.cover.symm.subset (Set.mem_iUnion.mpr ⟨i, T.projected_member i p.property⟩))

end Unfoldings.SpatialEnvelope.Triangulation
