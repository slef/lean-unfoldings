module

public import Unfoldings.Roof.TruncatedCutEmbedding
public import Unfoldings.Roof.CompatiblePotentialPaths
public import Unfoldings.Geometry.LocalPotentialGrowth

/-! The common potential increases on every truncated cut segment and through its mergers. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)
  (level : ℝ) (higher : ∀ v, G.height (K.projectedVertex v) < level)

theorem truncated_segment_follows (v : C.Vertex Set.univ) {s t : ℝ}
    (hs : 0 ≤ s) (ordered : s ≤ t) (ht : t ≤ 1) :
    R.FollowsStep
      (AffineMap.lineMap (R.truncatedPoint level (.inl v))
        (R.truncatedPoint level ((R.truncatedParents level higher).parent (.inl v))) s)
      (AffineMap.lineMap (R.truncatedPoint level (.inl v))
        (R.truncatedPoint level ((R.truncatedParents level higher).parent (.inl v))) t) := by
  by_cases root : v ∈ R.parents.roots
  · let r : {v // v ∈ R.parents.roots} := ⟨v, root⟩
    have parent := R.parents.withLeaves_parent_root level
      (fun v => (R.parent_height_le v).trans_lt (higher v)) r
    change (R.truncatedParents level higher).parent (.inl v) = .inr r at parent
    rw [parent]
    refine Or.inr ⟨r, s * R.terminalTime level r, t * R.terminalTime level r,
      mul_nonneg hs (R.terminalTime_pos level higher r).le,
      mul_le_mul_of_nonneg_right ordered (R.terminalTime_pos level higher r).le, ?_, ?_⟩
    · exact R.terminal_lineMap_eq_ray level r s
    · exact R.terminal_lineMap_eq_ray level r t
  · have parent := R.parents.withLeaves_parent_nonroot level
      (fun v => (R.parent_height_le v).trans_lt (higher v)) root
    change (R.truncatedParents level higher).parent (.inl v) = .inl (R.parents.parent v) at parent
    rw [parent]
    refine Or.inl ⟨⟨v, root⟩, s, t, hs, ordered, ht, ?_, ?_⟩
    all_goals
      dsimp [truncatedPoint, parentDirection]
      rw [AffineMap.lineMap_apply_module', add_comm]

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
theorem truncated_segment_strict (v : C.Vertex Set.univ) :
    StrictMonoOn (fun t : ℝ =>
      ((K.clippedExtension slopes compact nonempty).boundaryEnvelope boundary).height
        (AffineMap.lineMap (R.truncatedPoint level (.inl v))
          (R.truncatedPoint level ((R.truncatedParents level higher).parent (.inl v))) t))
      (Set.Icc 0 1) := by
  intro s hs t ht ordered
  have progress := R.followsStep_progress positive beta acute.le inner_disk
    (R.truncated_segment_follows level higher v hs.1 ordered.le ht.2)
  have coefficient : 0 < a * Real.cos β :=
    mul_pos positive (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], acute⟩)
  let e : {v // v ∉ (R.truncatedParents level higher).roots} :=
    ⟨.inl v, R.parents.withLeaves_inl_nonroot level _ v⟩
  let Q := K.truncatedCutEmbedding compact nonempty R no_boundary level higher
  have endpoint_ne : R.truncatedPoint level (.inl v) ≠
      R.truncatedPoint level ((R.truncatedParents level higher).parent (.inl v)) :=
    Q.vertex_injective.ne ((K.truncatedCutEmbedding_straight compact nonempty R
      no_boundary level higher).endpoints_ne e)
  have points_ne : AffineMap.lineMap (R.truncatedPoint level (.inl v))
      (R.truncatedPoint level ((R.truncatedParents level higher).parent (.inl v))) t ≠
        AffineMap.lineMap (R.truncatedPoint level (.inl v))
          (R.truncatedPoint level ((R.truncatedParents level higher).parent (.inl v))) s :=
    fun same => ordered.ne (AffineMap.lineMap_injective ℝ endpoint_ne same).symm
  have length := norm_pos_iff.mpr (sub_ne_zero.mpr points_ne)
  linarith [mul_pos coefficient length]

end Unfoldings.ConvexRoof
