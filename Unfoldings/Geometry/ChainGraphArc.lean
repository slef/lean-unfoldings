module

public import Unfoldings.Geometry.ChainLinearGraph
public import Unfoldings.Topology.IntervalArc

/-! Remove flat parametrization repetitions while retaining the whole chain image. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n) (height : E →L[ℝ] ℝ)
  (nonnegative : ∀ i, 0 ≤ height (P.edge i))
  (flat : ∀ i, height (P.edge i) = 0 → P.edge i = 0)

include nonnegative flat

/-- Strict progress between the endpoints turns the whole geometric chain image
into a simple arc. Its new parametrization traverses every original and gap segment. -/
theorem exists_injective_graph_path (positive : 0 < n)
    (progress : height (P.vertex 0) < height (P.vertex (Fin.last n))) :
    ∃ Q : Path (P.vertex 0) (P.vertex (Fin.last n)),
      Function.Injective Q ∧ Set.range Q = Set.range P.path := by
  let graph := P.linearGraphHomeomorph height nonnegative flat positive
  let first : Set.range P.path := ⟨P.vertex 0, 0, P.path.source⟩
  let last : Set.range P.path := ⟨P.vertex (Fin.last n), 1, P.path.target⟩
  have source : graph.symm ⟨height (P.vertex 0), le_rfl, progress.le⟩ = first := by
    apply graph.injective
    rw [graph.apply_symm_apply]
    apply Subtype.ext
    rfl
  have target : graph.symm ⟨height (P.vertex (Fin.last n)), progress.le, le_rfl⟩ = last := by
    apply graph.injective
    rw [graph.apply_symm_apply]
    apply Subtype.ext
    rfl
  let arc := intervalHomeomorphPath progress.le graph.symm
  refine ⟨arc.cast (congrArg Subtype.val source).symm (congrArg Subtype.val target).symm, ?_, ?_⟩
  · change Function.Injective arc
    exact intervalHomeomorphPath_injective progress graph.symm
  · change Set.range arc = Set.range P.path
    exact intervalHomeomorphPath_range progress.le graph.symm

end Unfoldings.PolygonalChain
