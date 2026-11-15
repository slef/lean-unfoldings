module

public import Unfoldings.Geometry.RadialClosingLinks
public import Unfoldings.Geometry.PolygonalClosureEquations
public import Unfoldings.Geometry.SegmentVertices

/-! A radial bank meets its actual closing arc only at the two bank endpoints. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n) (q c : Plane)

/-- The actual bank followed by its three literal closing links. -/
def radialClosurePieces : Fin 4 → Set Plane :=
  Fin.cases (Set.range P.path)
    (fun k => segment ℝ (radialClosingLinks q (P.vertex 0) (P.vertex (Fin.last n)) c k).1
      (radialClosingLinks q (P.vertex 0) (P.vertex (Fin.last n)) c k).2)

theorem radialClosurePieces_closed (j : Fin 4) : IsClosed (P.radialClosurePieces q c j) := by
  refine Fin.cases (isCompact_range P.path.continuous).isClosed (fun k => ?_) j
  exact (compact_segment _ _).isClosed

theorem threeSegmentClosure_subset_pieces :
    P.threeSegmentClosure q c ⊆ ⋃ j, P.radialClosurePieces q c j := by
  intro p member
  rcases member with bank | ((terminal | middle) | first)
  · exact Set.mem_iUnion.mpr ⟨0, bank⟩
  · exact Set.mem_iUnion.mpr ⟨1, terminal⟩
  · exact Set.mem_iUnion.mpr ⟨2, middle⟩
  · exact Set.mem_iUnion.mpr ⟨3, first⟩

/-- The geometric bank and its three-link complement have exactly their prescribed contacts. -/
theorem radial_bank_closing_contacts (radial : P.RadialFrom q 0)
    (initial : 0 < dist q (P.vertex 0)) (height : Plane →ₗ[ℝ] ℝ)
    (supported : ∀ z ∈ Set.range P.path, 0 ≤ height (z - q))
    (outside : height (c - q) < 0)
    (outward : 0 < inner ℝ (P.vertex (Fin.last n) - q) (c - P.vertex (Fin.last n))) :
    Set.range P.path ∩
      ((segment ℝ (P.vertex (Fin.last n)) c ∪ segment ℝ c q) ∪
        segment ℝ q (P.vertex 0)) = {P.vertex 0, P.vertex (Fin.last n)} := by
  ext z
  constructor
  · rintro ⟨on_bank, (terminal | middle) | first⟩
    · have same := terminal_segment_inter_radial_disk q (P.vertex (Fin.last n)) c outward
      have equal := Set.mem_singleton_iff.mp (same.subset
        ⟨terminal, (P.path_radius_bounds q radial on_bank).2⟩)
      exact Or.inr (Set.mem_singleton_iff.mpr equal)
    · rw [segment_symm ℝ c q] at middle
      have same := source_segments_inter height q z c (supported z on_bank) outside
      have equal := Set.mem_singleton_iff.mp (same.subset
        ⟨right_mem_segment ℝ _ _, middle⟩)
      have bound := (P.path_radius_bounds q radial on_bank).1
      rw [equal, dist_self] at bound
      exact (not_le_of_gt initial bound).elim
    · have same := initial_segment_inter_radial_exterior q (P.vertex 0)
      have equal := Set.mem_singleton_iff.mp (same.subset
        ⟨first, (P.path_radius_bounds q radial on_bank).1⟩)
      exact Or.inl equal
  · rintro (rfl | terminal)
    · exact ⟨⟨0, P.path.source⟩, Or.inr (right_mem_segment ℝ _ _)⟩
    · rw [Set.mem_singleton_iff.mp terminal]
      exact ⟨⟨1, P.path.target⟩, Or.inl (Or.inl (left_mem_segment ℝ _ _))⟩

open Classical in
/-- Distinct geometric closure pieces meet only at the four actual marked corners. -/
theorem radialClosurePieces_contacts (radial : P.RadialFrom q 0)
    (initial : 0 < dist q (P.vertex 0))
    (progress : dist q (P.vertex 0) < dist q (P.vertex (Fin.last n)))
    (height : Plane →ₗ[ℝ] ℝ) (supported : ∀ z ∈ Set.range P.path, 0 ≤ height (z - q))
    (outside : height (c - q) < 0)
    (outward : 0 < inner ℝ (P.vertex (Fin.last n) - q) (c - P.vertex (Fin.last n))) :
    ∀ j k, j ≠ k → P.radialClosurePieces q c j ∩ P.radialClosurePieces q c k ⊆
      (radialClosingCorners q (P.vertex 0) (P.vertex (Fin.last n)) c : Set Plane) := by
  have bank_contact (k : Fin 3) : P.radialClosurePieces q c 0 ∩
      P.radialClosurePieces q c k.succ ⊆
        (radialClosingCorners q (P.vertex 0) (P.vertex (Fin.last n)) c : Set Plane) := by
    intro z member
    have on_closing : z ∈ ((segment ℝ (P.vertex (Fin.last n)) c ∪ segment ℝ c q) ∪
        segment ℝ q (P.vertex 0)) := by
      fin_cases k
      · exact Or.inl (Or.inl member.2)
      · exact Or.inl (Or.inr member.2)
      · exact Or.inr member.2
    have contacts := P.radial_bank_closing_contacts q c radial initial height supported outside
      outward
    have at_endpoint := contacts.subset ⟨member.1, on_closing⟩
    rcases at_endpoint with first | last
    · simp [first, radialClosingCorners]
    · simp [Set.mem_singleton_iff.mp last, radialClosingCorners]
  have links_contact := radialClosingLinks_contacts q (P.vertex 0)
    (P.vertex (Fin.last n)) c progress height (supported _ ⟨0, P.path.source⟩)
    (supported _ ⟨1, P.path.target⟩) outside outward
  intro j k
  refine Fin.cases ?_ (fun a => ?_) j
  · refine Fin.cases (fun different => (different rfl).elim)
      (fun b _different => bank_contact b) k
  · refine Fin.cases (fun _different z member => bank_contact a ⟨member.2, member.1⟩)
      (fun b different => links_contact a b (fun same => different (congrArg Fin.succ same))) k

end Unfoldings.PolygonalChain
