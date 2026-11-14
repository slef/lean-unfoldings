module

public import Unfoldings.Geometry.HingeGap
public import Unfoldings.Geometry.RaySplitRadius
public import Unfoldings.Geometry.RotationGapSweep

/-! A radial hinge gap cannot invade the prefix kept fixed by the opening. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n)

theorem rotateSuffix_prefix (hinge : Fin (n + 1)) (angle : ℝ) :
    (R.rotateSuffix hinge angle).chain.interval 0 hinge.val (by omega) =
      R.chain.interval 0 hinge.val (by omega) := by
  apply congrArg (PolygonalChain.mk (E := ℂ) (n := hinge.val))
  funext i
  change (R.chain.rotateSuffix hinge angle).vertex ⟨0 + i.val, by omega⟩ =
    R.chain.vertex ⟨0 + i.val, by omega⟩
  exact R.chain.rotateSuffix_vertex_le hinge angle _ (by change 0 + i.val ≤ hinge.val; omega)

/-- Uniform radial control throughout an opening proves disjointness from the unchanged prefix. -/
theorem hingeGap_prefix_inter (hinge : Fin (n + 1)) (outward : (R.suffix hinge).Outward)
    (nonzero : R.direction ≠ 0) (angle : ℝ) (positive : 0 < angle) (small : angle < Real.pi)
    (radial : ∀ θ ∈ Set.Icc 0 angle, (R.rotateSuffix hinge θ).Outward) :
    Set.range (R.chain.interval 0 hinge.val (by omega)).path ∩
      (R.suffix hinge).rotationGap outward nonzero angle = {R.chain.vertex hinge} := by
  ext z
  constructor
  · rintro ⟨kept, in_gap⟩
    obtain ⟨θ, heading, bank⟩ :=
      ((R.suffix hinge).mem_rotationGap_iff_sweep outward nonzero angle positive small z).mp in_gap
    have nonzero_rotated : (R.rotateSuffix hinge θ).direction ≠ 0 := by
      change complexRotation θ R.direction ≠ 0
      simpa only [map_zero] using (complexRotation θ).injective.ne nonzero
    have kept_rotated : z ∈ Set.range
        ((R.rotateSuffix hinge θ).chain.interval 0 hinge.val (by omega)).path := by
      rw [R.rotateSuffix_prefix]
      exact kept
    have bank_rotated : z ∈ ((R.rotateSuffix hinge θ).suffix hinge).carrier := by
      rw [R.rotateSuffix_suffix_carrier]
      exact bank
    have intersection := (R.rotateSuffix hinge θ).prefix_suffix_inter (radial θ heading)
      nonzero_rotated hinge
    have member := (Set.ext_iff.mp intersection z).mp ⟨kept_rotated, bank_rotated⟩
    simpa only [rotateSuffix, PolygonalChain.rotateSuffix_vertex_le _ _ _ _ le_rfl] using member
  · rintro rfl
    constructor
    · have endpoint := (R.chain.interval 0 hinge.val (by omega)).vertex_mem_path_range (Fin.last _)
      simpa only [PolygonalChain.interval_last, Nat.zero_add, Fin.eta] using endpoint
    · apply ((R.suffix hinge).mem_rotationGap_iff_sweep outward nonzero angle positive small _).mpr
      refine ⟨0, ⟨le_rfl, positive.le⟩, (R.suffix hinge).start, (R.suffix hinge).start_mem, ?_⟩
      simp

end Unfoldings.PolygonalRay
