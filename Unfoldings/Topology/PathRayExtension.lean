module

public import Unfoldings.Metric.DilationIntervalPath
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Analysis.Convex.PathConnected

/-! Continue an actual finite path along a joined metric half-line without an outer truncation. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings

variable {X : Type*} [EMetricSpace X] {a b : X} (P : Path a b)
  (f : ℝ≥0 →ᵈ X) (start : ℝ≥0) (joined : b = f start)

/-- Traverse the finite original path on `[0,1]`, then its whole joined original tail. -/
def pathRayExtension (t : ℝ≥0) : X :=
  if before : t.val ≤ 1 then P ⟨t.val, t.property, before⟩
  else f (start + ⟨t.val - 1, by linarith [t.property]⟩)

/-- On the initial interval the extension is the literal original intrinsic path. -/
theorem pathRayExtension_path (t : unitInterval) :
    pathRayExtension P f start ⟨t.val, t.property.1⟩ = P t := by
  unfold pathRayExtension
  rw [dite_eq_left t.property.2]

include joined

/-- On the whole infinite tail the original dilation parameter is preserved. -/
theorem pathRayExtension_tail (t : ℝ≥0) :
    pathRayExtension P f start (1 + t) = f (start + t) := by
  by_cases zero : t = 0
  · subst t
    have endpoint := P.target.trans joined
    simpa [pathRayExtension] using endpoint
  · have positive : 0 < t.val := lt_of_le_of_ne t.property (fun same => zero (Subtype.ext
    same.symm))
    unfold pathRayExtension
    rw [dite_eq_right (by change ¬ 1 + t.val ≤ 1; linarith)]
    congr 2
    apply Subtype.ext
    change 1 + t.val - 1 = t.val
    ring

/-- The finite stem and original infinite tail join continuously in the actual metric space. -/
theorem continuous_pathRayExtension : Continuous (pathRayExtension P f start) := by
  have expression : pathRayExtension P f start = fun t : ℝ≥0 =>
      if t.val ≤ 1 then P.extend t.val else f (start + Real.toNNReal (t.val - 1)) := by
    funext t
    unfold pathRayExtension
    split_ifs with before
    · exact (P.extend_extends' ⟨t.val, t.property, before⟩).symm
    · congr 2
      apply Subtype.ext
      exact (Real.coe_toNNReal (t.val - 1) (by linarith : 0 ≤ t.val - 1)).symm
  rw [expression]
  apply continuous_if_le continuous_subtype_val continuous_const
  · exact (P.continuous_extend.comp continuous_subtype_val).continuousOn
  · exact ((Dilation.lipschitzWith f).continuous.comp
      (continuous_const.add (continuous_real_toNNReal.comp
        (continuous_subtype_val.sub continuous_const)))).continuousOn
  · intro t same
    rw [same, sub_self, Real.toNNReal_zero, add_zero, P.extend_one]
    exact joined

/-- No original bank point is lost and no auxiliary path points are introduced. -/
theorem pathRayExtension_range : Set.range (pathRayExtension P f start) =
    Set.range P ∪ f '' Set.Ici start := by
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    unfold pathRayExtension
    split_ifs with before
    · exact Or.inl ⟨_, rfl⟩
    · refine Or.inr ⟨_, ?_, rfl⟩
      change start.val ≤ start.val + (t.val - 1)
      linarith
  · rintro x (⟨t, rfl⟩ | ⟨t, after, rfl⟩)
    · exact ⟨⟨t.val, t.property.1⟩, pathRayExtension_path P f start t⟩
    · let elapsed : ℝ≥0 := ⟨t.val - start.val, sub_nonneg.mpr after⟩
      have same : start + elapsed = t := by
        apply Subtype.ext
        change start.val + (t.val - start.val) = t.val
        ring
      exact ⟨1 + elapsed, (pathRayExtension_tail P f start joined elapsed).trans (congrArg f same)⟩

/-- The whole continued carrier is closed, including the entire unbounded tail. -/
theorem isClosed_pathRayExtension_range : IsClosed (Set.range (pathRayExtension P f start)) := by
  rw [pathRayExtension_range P f start joined]
  exact (isCompact_range P.continuous).isClosed.union
    ((Dilation.isClosedEmbedding f).isClosedMap _ isClosed_Ici)

/-- The whole original bank is path connected without choosing an outer terminal time. -/
theorem isPathConnected_pathRayExtension_range :
    IsPathConnected (Set.range (pathRayExtension P f start)) := by
  have surjective : Function.Surjective Real.toNNReal := fun t =>
    ⟨t.val, by exact Real.toNNReal_coe⟩
  let : PathConnectedSpace ℝ≥0 := surjective.pathConnectedSpace continuous_real_toNNReal
  exact isPathConnected_range (continuous_pathRayExtension P f start joined)

/-- Separation of the positive tail identifies the only intersection of the two complete
closed pieces. The final parameter is allowed to tend to infinity. -/
theorem path_inter_dilation_ray
    (separated : ∀ u : ℝ≥0, start < u → f u ∉ Set.range P) :
    Set.range P ∩ f '' Set.Ici start = {f start} := by
  apply Set.Subset.antisymm
  · rintro x ⟨on_path, u, after, at_x⟩
    have at_start : u = start := by
      apply Subtype.ext
      apply le_antisymm ?_ after
      by_contra later
      exact separated u (lt_of_not_ge later) (at_x ▸ on_path)
    exact Set.mem_singleton_iff.mpr (at_x.symm.trans (congrArg f at_start))
  · intro x member
    rw [Set.mem_singleton_iff.mp member]
    exact ⟨⟨1, P.target.trans joined⟩, start, le_rfl, rfl⟩

end Unfoldings
