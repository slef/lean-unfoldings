module

public import Unfoldings.Roof.CompatibleTerminalBanks

/-! Reusable actual whole-cut partitions retain their geometric side assignments. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

/-- One actual complete partition, with its original geometric cut-side assignments retained. -/
structure WholeCutModel (M : G.FiniteSlopeModel) where
  Index : Type
  finiteIndex : Fintype Index
  partition : SpatialEnvelope.WholePartition M.plane Index
  signs : Index → Fin (Fintype.card (C.Vertex Set.univ)) → Bool
  aligned : ∀ c x, x ∈ partition.footprint c → ∀ i,
    0 ≤ AffineArrangement.signed (R.wholeCutEquation i) (signs c i) x

attribute [instance] WholeCutModel.finiteIndex

/-- Construct one whole unbounded cut model, for reuse through subsequent geometric proofs. -/
def wholeCutModel (M : G.FiniteSlopeModel) : R.WholeCutModel M :=
  Classical.choice (by
    obtain ⟨A, finite, P, signs, aligned⟩ := SpatialEnvelope.exists_wholePartition M.plane
      R.wholeCutEquation R.wholeCutEquation_ne_zero
    exact ⟨⟨A, finite, P, signs, aligned⟩⟩)

namespace WholeCutModel

variable {R} {M : G.FiniteSlopeModel} (W : R.WholeCutModel M)

/-- The actual complete cut metric belonging to this retained partition. -/
abbrev Cut := W.partition.Cut R.carrier

theorem complete : CompleteSpace W.Cut := W.partition.cut_complete R.carrier

theorem restore_surjective : Function.Surjective (W.partition.restoreCut R.carrier) :=
  W.partition.restoreCut_surjective R.carrier

theorem carrier_boundary : R.carrier ⊆ ⋃ a, frontier (W.partition.footprint a) := by
  intro x member
  obtain ⟨i, zero⟩ := R.carrier_covered_by_wholeCutEquations x member
  have covered : x ∈ ⋃ a, W.partition.footprint a := W.partition.cover.symm ▸ Set.mem_univ x
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp covered
  exact Set.mem_iUnion.mpr ⟨a, W.partition.mem_frontier_of_constraint R.wholeCutEquation
    R.wholeCutEquation_ne_zero W.signs W.aligned a ha i zero⟩

/-- The exact original side assignment along a named actual terminal ray. -/
def terminalSigns (r : {v // v ∈ R.parents.roots}) : W.Index → Bool :=
  fun c => W.signs c ((Fintype.equivFin (C.Vertex Set.univ)) r.val)

theorem terminal_aligned (r : {v // v ∈ R.parents.roots}) :
    ∀ c x, x ∈ W.partition.footprint c →
      0 ≤ AffineArrangement.signed
        (orientMap (K.projectedVertex r.val) (R.wholeCutLast r.val)) (W.terminalSigns r c) x := by
  intro c x hx
  have lower := W.aligned c x hx ((Fintype.equivFin (C.Vertex Set.univ)) r.val)
  rwa [R.terminal_orient_equation r] at lower

end WholeCutModel
end Unfoldings.ConvexRoof.CompatiblePotentialRouting
