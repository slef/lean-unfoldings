module

public import Unfoldings.Roof.TruncatedCutProgress

/-! The entire bounded cut carrier has local common-potential growth away from its boundary. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)
  (level : ℝ) (higher : ∀ v, G.height (K.projectedVertex v) < level)

def truncatedCarrier : Set Plane :=
  ⋃ v : C.Vertex Set.univ, segment ℝ (R.truncatedPoint level (.inl v))
    (R.truncatedPoint level ((R.truncatedParents level higher).parent (.inl v)))

theorem vertex_mem_truncatedCarrier (v : C.Vertex Set.univ) :
    K.projectedVertex v ∈ R.truncatedCarrier level higher :=
  Set.mem_iUnion.mpr ⟨v, left_mem_segment ℝ _ _⟩

theorem truncatedCarrier_subset_sublevel :
    R.truncatedCarrier level higher ⊆ {x | G.height x ≤ level} := by
  have sublevel : Convex ℝ {x | G.height x ≤ level} := by
    simpa only [Set.mem_univ, true_and] using G.convex_height.convex_le level
  intro x member
  obtain ⟨v, on_edge⟩ := Set.mem_iUnion.mp member
  exact sublevel.segment_subset (higher v).le (R.truncated_parent_height_le level higher v) on_edge

end Unfoldings.ConvexRoof.CompatiblePotentialRouting

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)
  (positive : 0 < a) (beta : 0 ≤ β) (acute : β < Real.pi / 2)
  (inner_disk : Metric.ball (0 : Plane) a ⊆ slopes)

include no_boundary positive beta acute inner_disk in
theorem truncated_growth_at_vertex (v : C.Vertex Set.univ) :
    LocalPotentialGrowth (R.truncatedCarrier level higher)
      ((K.clippedExtension slopes compact nonempty).boundaryEnvelope boundary).height
      (K.projectedVertex v) := by
  have strict := K.truncated_segment_strict compact nonempty R no_boundary level higher
    positive beta acute inner_disk v
  apply LocalPotentialGrowth.mono (localPotentialGrowth_of_segment_strict strict
    (left_mem_segment ℝ _ _) ?_) (fun _ on_segment => Set.mem_iUnion.mpr ⟨v, on_segment⟩)
  intro equal
  have increase := strict (show (0 : ℝ) ∈ Set.Icc 0 1 by simp)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by simp) zero_lt_one
  dsimp only at increase
  rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, equal] at increase
  exact lt_irrefl _ increase

include no_boundary positive beta acute inner_disk in
theorem truncated_local_growth {p : Plane} (member : p ∈ R.truncatedCarrier level higher)
    (inside : p ∈ interior {x | (K.clippedExtension slopes compact nonempty).height x ≤ level}) :
    LocalPotentialGrowth (R.truncatedCarrier level higher ∩
      interior {x | (K.clippedExtension slopes compact nonempty).height x ≤ level})
      ((K.clippedExtension slopes compact nonempty).boundaryEnvelope boundary).height p := by
  apply LocalPotentialGrowth.inter_open (open_U := isOpen_interior) (member := inside)
  obtain ⟨v, on_edge⟩ := Set.mem_iUnion.mp member
  by_cases last : p = R.truncatedPoint level
      ((R.truncatedParents level higher).parent (.inl v))
  · cases parent : (R.truncatedParents level higher).parent (.inl v) with
    | inl w =>
      rw [parent] at last
      exact last ▸ K.truncated_growth_at_vertex compact nonempty R no_boundary level higher
        positive beta acute inner_disk w
    | inr r =>
      rw [parent] at last
      change p = R.terminalPoint level r at last
      have frontier := R.terminalPoint_mem_frontier level higher r
      exact (frontier.2 (last ▸ inside)).elim
  · exact (localPotentialGrowth_of_segment_strict
      (K.truncated_segment_strict compact nonempty R no_boundary level higher
        positive beta acute inner_disk v) on_edge last).mono
          (fun _ on_segment => Set.mem_iUnion.mpr ⟨v, on_segment⟩)

end Unfoldings.ConvexRoof
