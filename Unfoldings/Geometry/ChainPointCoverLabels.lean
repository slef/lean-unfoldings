module

public import Unfoldings.Geometry.ChainCoverWedges

/-! Every point of a covered fine chain retains its starting geometric component label. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E I A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Finite I]
  {n : ℕ} (P : PolygonalChain E n)

theorem point_label_eq_of_segment_cover (first last : I → E) (label : I → A)
    (compatible : ∀ i j, (segment ℝ (first i) (last i) ∩
      segment ℝ (first j) (last j)).Nonempty → label i = label j)
    (cover : ∀ i : Fin n, segment ℝ (P.vertex i.castSucc) (P.vertex i.succ) ⊆
      ⋃ j, segment ℝ (first j) (last j))
    (anchor : I) (start : P.vertex 0 ∈ segment ℝ (first anchor) (last anchor))
    (j : Fin n) (s : unitInterval) (i : I)
    (member : P.point j s ∈ segment ℝ (first i) (last i)) :
    label i = label anchor := by
  obtain ⟨k, at_start⟩ := Set.mem_iUnion.mp ((cover j) (left_mem_segment ℝ _ _))
  have component := P.labels_eq_of_segment_cover first last label compatible cover anchor start
    j.castSucc k at_start
  have within : P.point j s ∈ segment ℝ (P.vertex j.castSucc) (P.vertex j.succ) :=
    lineMap_mem_segment ℝ _ _ s.property
  exact (segment_cover_labels_eq first last label compatible (cover j)
    ⟨P.point j s, within, member⟩ ⟨P.vertex j.castSucc, left_mem_segment ℝ _ _, at_start⟩).trans
      component

end Unfoldings.PolygonalChain
