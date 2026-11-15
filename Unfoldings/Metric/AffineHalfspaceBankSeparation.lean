module

public import Unfoldings.Metric.AffineHalfspaceBank
public import Unfoldings.Metric.AffineCutBanks

/-! Canonical halfspace banks are closed, and locally complete cuts distinguish their copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite I]
  (cells : I → Set E) (closed : ∀ i, IsClosed (cells i))
  (convex : ∀ i, Convex ℝ (cells i)) (full : ∀ i, (interior (cells i)).Nonempty)
  (cover : (⋃ i, cells i) = Set.univ) (f : E →ᵃ[ℝ] ℝ) (proper : f ≠ 0)
  (signs : I → Bool)
  (aligned : ∀ i x, x ∈ cells i → 0 ≤ AffineArrangement.signed f (signs i) x)
  (side : Bool) (positive : ∃ q, 0 < AffineArrangement.signed f side q)
  (cuts : Set E) (cut_closed : IsClosed cuts) (cut_level : ∀ x ∈ cuts, f x = 0)

/-- Different canonical sides give different actual metric points along a locally complete cut. -/
theorem affineHalfspaceBanks_ne_of_local_cut
    (other : Bool) (other_positive : ∃ q, 0 < AffineArrangement.signed f other q)
    (different : side ≠ other) {W : Set E} (open_W : IsOpen W)
    (local_cut : ∀ z ∈ W, f z = 0 → z ∈ cuts)
    (x : {x | 0 ≤ AffineArrangement.signed f side x})
    (y : {x | 0 ≤ AffineArrangement.signed f other x}) (inside : x.val ∈ W) :
    affineHalfspaceBank cells closed convex full cover f proper signs aligned side positive
      cuts cut_closed cut_level x ≠
    affineHalfspaceBank cells closed convex full cover f proper signs aligned other other_positive
      cuts cut_closed cut_level y := by
  obtain ⟨i, imem⟩ := Set.mem_iUnion.mp
    ((affineHalfspace_eq_iUnion cells closed f signs cover aligned side positive).subset x.property)
  obtain ⟨j, jmem⟩ := Set.mem_iUnion.mp
    ((affineHalfspace_eq_iUnion cells closed f signs cover aligned other other_positive).subset
      y.property)
  rw [affineHalfspaceBank_eq_of_mem cells closed convex full cover f proper signs aligned side
    positive cuts cut_closed cut_level x i imem,
    affineHalfspaceBank_eq_of_mem cells closed convex full cover f proper signs aligned other
      other_positive cuts cut_closed cut_level y j jmem]
  apply cut_of_ne_of_opposite_sign cells closed cuts f signs aligned open_W local_cut
    ⟨x.val, imem⟩ ⟨y.val, jmem⟩ inside
  rwa [i.property, j.property]

/-- In finite-dimensional complete coordinates, an entire bank halfspace is closed and embedded. -/
theorem affineHalfspaceBank_isClosedEmbedding [FiniteDimensional ℝ E] [CompleteSpace E] :
    Topology.IsClosedEmbedding
      (affineHalfspaceBank cells closed convex full cover f proper signs aligned side positive
        cuts cut_closed cut_level) := by
  have closed_side : IsClosed {x | 0 ≤ AffineArrangement.signed f side x} :=
    isClosed_le continuous_const (AffineArrangement.signed f side).continuous_of_finiteDimensional
  let : CompleteSpace {x | 0 ≤ AffineArrangement.signed f side x} :=
    closed_side.isComplete.completeSpace_coe
  exact (affineHalfspaceBank_isometry cells closed convex full cover f proper signs aligned
    side positive cuts cut_closed cut_level).isClosedEmbedding

end Unfoldings.MetricGluing
