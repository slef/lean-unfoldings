module

public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Homeomorph.Lemmas

/-! A set homeomorphic to a nondegenerate real interval is the image of an injective path. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- The ordinary segment parameter, retaining membership in the closed coordinate interval. -/
def intervalSegmentPoint {a b : ℝ} (ordered : a ≤ b) (t : unitInterval) : Set.Icc a b :=
  ⟨Path.segment a b t, (convex_Icc a b).lineMap_mem ⟨le_rfl, ordered⟩
    ⟨ordered, le_rfl⟩ t.property⟩

variable {X : Type*} [TopologicalSpace X] {S : Set X} {a b : ℝ}

/-- Traverse a homeomorphic interval in its coordinate order, preserving its entire image. -/
def intervalHomeomorphPath (ordered : a ≤ b) (e : Set.Icc a b ≃ₜ S) :
    Path (e ⟨a, le_rfl, ordered⟩).val (e ⟨b, ordered, le_rfl⟩).val where
  toFun t := (e (intervalSegmentPoint ordered t)).val
  continuous_toFun := continuous_subtype_val.comp (e.continuous.comp
    ((Path.segment a b).continuous.subtype_mk _))
  source' := congrArg (fun x : Set.Icc a b => (e x).val)
    (Subtype.ext (Path.segment a b).source)
  target' := congrArg (fun x : Set.Icc a b => (e x).val)
    (Subtype.ext (Path.segment a b).target)

theorem intervalHomeomorphPath_range (ordered : a ≤ b) (e : Set.Icc a b ≃ₜ S) :
    Set.range (intervalHomeomorphPath ordered e) = S := by
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    exact (e (intervalSegmentPoint ordered t)).property
  · intro x member
    let c := e.symm ⟨x, member⟩
    have on_segment : c.val ∈ segment ℝ a b := (segment_eq_Icc ordered).symm.subset c.property
    obtain ⟨t, equal⟩ := (Path.range_segment a b).symm.subset on_segment
    have same : intervalSegmentPoint ordered t = c := Subtype.ext equal
    refine ⟨t, ?_⟩
    change (e (intervalSegmentPoint ordered t)).val = x
    rw [same]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, member⟩)

theorem intervalHomeomorphPath_injective (ordered : a < b) (e : Set.Icc a b ≃ₜ S) :
    Function.Injective (intervalHomeomorphPath ordered.le e) := by
  intro s t equal
  have values : intervalSegmentPoint ordered.le s = intervalSegmentPoint ordered.le t :=
    e.injective (Subtype.ext equal)
  apply Subtype.ext
  exact AffineMap.lineMap_injective ℝ (ne_of_lt ordered) (congrArg Subtype.val values)

end Unfoldings
