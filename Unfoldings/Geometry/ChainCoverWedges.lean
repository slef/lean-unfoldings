module

public import Unfoldings.Geometry.SegmentCoverLabels

/-! Finite meshed paths inherit one acute wedge from their consistently labeled cut component. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E I A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Finite I]
  {n : ℕ} (P : PolygonalChain E n)

/-- Consistent component labels propagate across every successive whole edge. -/
theorem labels_eq_of_segment_cover (first last : I → E) (label : I → A)
    (compatible : ∀ i j, (segment ℝ (first i) (last i) ∩
      segment ℝ (first j) (last j)).Nonempty → label i = label j)
    (cover : ∀ i : Fin n, segment ℝ (P.vertex i.castSucc) (P.vertex i.succ) ⊆
      ⋃ j, segment ℝ (first j) (last j))
    (anchor : I) (start : P.vertex 0 ∈ segment ℝ (first anchor) (last anchor))
    (j : Fin (n + 1)) (i : I) (member : P.vertex j ∈ segment ℝ (first i) (last i)) :
    label i = label anchor := by
  have along (j : Fin (n + 1)) :
      ∀ i, P.vertex j ∈ segment ℝ (first i) (last i) → label i = label anchor := by
    induction j using Fin.induction with
    | zero => exact fun i member => compatible i anchor ⟨P.vertex 0, member, start⟩
    | succ j ih =>
      intro i member
      obtain ⟨k, at_start⟩ := Set.mem_iUnion.mp ((cover j) (left_mem_segment ℝ _ _))
      have equal := segment_cover_labels_eq first last label compatible (cover j)
        ⟨P.vertex j.castSucc, left_mem_segment ℝ _ _, at_start⟩
        ⟨P.vertex j.succ, right_mem_segment ℝ _ _, member⟩
      exact equal.symm.trans (ih k at_start)
  exact along j i member

/-- No count of subdivisions appears: every directed fine edge belongs to the same component
wedge. Constant edges are allowed and contribute the zero vector. -/
theorem directions_of_labeled_segment_cover (q u v : E) (first last : I → E) (label : I → A)
    (outward : ∀ i : Fin n, 0 ≤ inner ℝ (P.vertex i.castSucc - q) (P.edge i))
    (piece_outward : ∀ i, 0 ≤ inner ℝ (first i - q) (last i - first i))
    (compatible : ∀ i j, (segment ℝ (first i) (last i) ∩
      segment ℝ (first j) (last j)).Nonempty → label i = label j)
    (cover : ∀ i : Fin n, segment ℝ (P.vertex i.castSucc) (P.vertex i.succ) ⊆
      ⋃ j, segment ℝ (first j) (last j))
    (anchor : I) (start : P.vertex 0 ∈ segment ℝ (first anchor) (last anchor))
    (directions : ∀ j, label j = label anchor → InDirectionWedge u v (last j - first j)) :
    ∀ i, InDirectionWedge u v (P.edge i) := by
  intro i
  by_cases equal : P.vertex i.castSucc = P.vertex i.succ
  · refine ⟨0, 0, le_rfl, le_rfl, ?_⟩
    simp only [edge, equal, sub_self, zero_smul, add_zero]
  · obtain ⟨k, at_start⟩ := Set.mem_iUnion.mp ((cover i) (left_mem_segment ℝ _ _))
    have component := P.labels_eq_of_segment_cover first last label compatible cover anchor start
      i.castSucc k at_start
    exact direction_wedge_of_labeled_segment_cover q _ _ u v equal (outward i) first last label
      piece_outward compatible (cover i) k
      ⟨P.vertex i.castSucc, left_mem_segment ℝ _ _, at_start⟩
      (fun j same => directions j (same.trans component))

/-- An acute wedge of the original component is also an acute wedge of every finite meshed path
that follows it outward, including paths through branches and flat subdivision vertices. -/
theorem angleMonotone_of_labeled_segment_cover (q u v : E) (first last : I → E) (label : I → A)
    (outward : ∀ i : Fin n, 0 ≤ inner ℝ (P.vertex i.castSucc - q) (P.edge i))
    (piece_outward : ∀ i, 0 ≤ inner ℝ (first i - q) (last i - first i))
    (compatible : ∀ i j, (segment ℝ (first i) (last i) ∩
      segment ℝ (first j) (last j)).Nonempty → label i = label j)
    (cover : ∀ i : Fin n, segment ℝ (P.vertex i.castSucc) (P.vertex i.succ) ⊆
      ⋃ j, segment ℝ (first j) (last j))
    (anchor : I) (start : P.vertex 0 ∈ segment ℝ (first anchor) (last anchor))
    (directions : ∀ j, label j = label anchor → InDirectionWedge u v (last j - first j))
    (first_ne : u ≠ 0) (last_ne : v ≠ 0) : P.AngleMonotone (InnerProductGeometry.angle u v) :=
  ⟨u, v, first_ne, last_ne, le_rfl,
    P.directions_of_labeled_segment_cover q u v first last label outward piece_outward
      compatible cover anchor start directions⟩

end Unfoldings.PolygonalChain
