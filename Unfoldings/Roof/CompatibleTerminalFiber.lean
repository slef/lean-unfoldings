module

public import Unfoldings.Roof.CompatibleTerminalExcision
public import Unfoldings.Geometry.SpatialEnvelopeCutFiber
public import Unfoldings.Metric.LocalIsometricLift

/-! Every positive original terminal bank copy has a unique full-forest metric preimage. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  {M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel} (W : R.WholeCutModel M)

local instance terminalFiberIndexFintype : Fintype W.Index := W.finiteIndex

include no_boundary in
/-- Restoring other cuts preserves the entire original metric fiber at a positive terminal point.
There is a unique original full-forest copy above each one-ray-cut bank copy. -/
theorem existsUnique_terminalRayCut_preimage (r : {v // v ∈ R.parents.roots}) {t : ℝ}
    (positive : 0 < t) (y : W.partition.Cut (R.terminalRayCut r))
    (position : Cap.horizontal (W.partition.restoreCut (R.terminalRayCut r) y).val =
      R.exterior.ray (R.terminalIndex r) t) :
    ∃! x : W.Cut, W.partition.forgetCut R.carrier (R.terminalRayCut r)
      (R.terminalRayCut_subset_carrier r) x = y := by
  obtain ⟨x, image⟩ := W.partition.forgetCut_surjective R.carrier (R.terminalRayCut r)
    (R.terminalRayCut_subset_carrier r) y
  have horizontal : Cap.horizontal (W.partition.restoreCut R.carrier x).val =
      R.exterior.ray (R.terminalIndex r) t := by
    have restored := W.partition.restoreCut_forgetCut R.carrier (R.terminalRayCut r)
      (R.terminalRayCut_subset_carrier r) x
    exact (congrArg (fun p => Cap.horizontal p.val) restored).symm.trans
      ((congrArg (fun z => Cap.horizontal
        (W.partition.restoreCut (R.terminalRayCut r) z).val) image).trans position)
  obtain ⟨ε, εpos, same⟩ := K.exists_terminalRayCut_germ compact nonempty R no_boundary r positive
  refine ⟨x, image, ?_⟩
  intro z hz
  apply W.partition.forgetCut_injective_at_of_local_eq R.carrier (R.terminalRayCut r)
    (R.terminalRayCut_subset_carrier r) z εpos
  · have restored_z := W.partition.restoreCut_forgetCut R.carrier (R.terminalRayCut r)
      (R.terminalRayCut_subset_carrier r) z
    have z_position : Cap.horizontal (W.partition.restoreCut R.carrier z).val =
        R.exterior.ray (R.terminalIndex r) t :=
      (congrArg (fun p => Cap.horizontal p.val) restored_z).symm.trans
        ((congrArg (fun w => Cap.horizontal
          (W.partition.restoreCut (R.terminalRayCut r) w).val) hz).trans position)
    simpa only [z_position] using same
  · exact hz.trans image.symm

/-- The unique actual full-forest lift of a positive terminal-bank curve. -/
def terminalRayLift (r : {v // v ∈ R.parents.roots})
    (g : Set.Ioi (0 : ℝ) → W.partition.Cut (R.terminalRayCut r))
    (position : ∀ t, Cap.horizontal (W.partition.restoreCut (R.terminalRayCut r) (g t)).val =
      R.exterior.ray (R.terminalIndex r) t.val) : Set.Ioi (0 : ℝ) → W.Cut :=
  fun t => (K.existsUnique_terminalRayCut_preimage compact nonempty R no_boundary W r
    t.property (g t) (position t)).choose

@[simp] theorem forgetCut_terminalRayLift (r : {v // v ∈ R.parents.roots})
    (g : Set.Ioi (0 : ℝ) → W.partition.Cut (R.terminalRayCut r))
    (position : ∀ t, Cap.horizontal (W.partition.restoreCut (R.terminalRayCut r) (g t)).val =
      R.exterior.ray (R.terminalIndex r) t.val) (t : Set.Ioi (0 : ℝ)) :
    W.partition.forgetCut R.carrier (R.terminalRayCut r) (R.terminalRayCut_subset_carrier r)
      (K.terminalRayLift compact nonempty R no_boundary W r g position t) = g t :=
  (K.existsUnique_terminalRayCut_preimage compact nonempty R no_boundary W r
    t.property (g t) (position t)).choose_spec.1

theorem restoreCut_terminalRayLift (r : {v // v ∈ R.parents.roots})
    (g : Set.Ioi (0 : ℝ) → W.partition.Cut (R.terminalRayCut r))
    (position : ∀ t, Cap.horizontal (W.partition.restoreCut (R.terminalRayCut r) (g t)).val =
      R.exterior.ray (R.terminalIndex r) t.val) (t : Set.Ioi (0 : ℝ)) :
    W.partition.restoreCut R.carrier
      (K.terminalRayLift compact nonempty R no_boundary W r g position t) =
        W.partition.restoreCut (R.terminalRayCut r) (g t) :=
  (W.partition.restoreCut_forgetCut R.carrier (R.terminalRayCut r)
    (R.terminalRayCut_subset_carrier r) _).symm.trans
      (congrArg (W.partition.restoreCut (R.terminalRayCut r))
        (K.forgetCut_terminalRayLift compact nonempty R no_boundary W r g position t))

/-- Lifting a terminal bank to the full forest does not increase its Lipschitz constant.
The proof uses whole-ball restoration and global uniqueness of the actual physical fibers. -/
theorem terminalRayLift_lipschitz (r : {v // v ∈ R.parents.roots})
    (g : Set.Ioi (0 : ℝ) → W.partition.Cut (R.terminalRayCut r))
    (position : ∀ t, Cap.horizontal (W.partition.restoreCut (R.terminalRayCut r) (g t)).val =
      R.exterior.ray (R.terminalIndex r) t.val)
    (c : ℝ≥0) (bounded : LipschitzWith c g) :
    LipschitzWith c (K.terminalRayLift compact nonempty R no_boundary W r g position) := by
  let f := K.terminalRayLift compact nonempty R no_boundary W r g position
  let F := W.partition.forgetCut R.carrier (R.terminalRayCut r)
    (R.terminalRayCut_subset_carrier r)
  apply lipschitzWith_lift_of_ball_charts (Set.Ioi (0 : ℝ)) (convex_Ioi 0) f g F c bounded
  · intro t x image
    exact (K.existsUnique_terminalRayCut_preimage compact nonempty R no_boundary W r
      t.property (g t) (position t)).choose_spec.2 x image
  · intro t
    have original_position : Cap.horizontal (W.partition.restoreCut R.carrier (f t)).val =
        R.exterior.ray (R.terminalIndex r) t.val :=
      (congrArg (fun p => Cap.horizontal p.val)
        (K.restoreCut_terminalRayLift compact nonempty R no_boundary W r g position t)).trans
          (position t)
    obtain ⟨ε, εpos, B, agrees⟩ := K.exists_terminalRayCut_ball_chart compact nonempty R
      no_boundary W r t.property (f t) original_position
    have image : F (f t) = g t :=
      K.forgetCut_terminalRayLift compact nonempty R no_boundary W r g position t
    rw [← image]
    exact ⟨ε, εpos, B, agrees⟩

end Unfoldings.ConvexRoof
