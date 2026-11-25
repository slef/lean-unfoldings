module

public import Unfoldings.Geometry.MinorArcConnectivity
public import Mathlib.Topology.Homotopy.Basic

/-! Pointwise nonantipodal sphere maps are joined by normalized chord interpolation. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- The unit sphere homotopy follows the normalized positive chord at every site. -/
def sphericalShortHomotopy {X : Type*} [TopologicalSpace X]
    (f g : C(X, Metric.sphere (0 : Space) 1))
    (nonantipodal : ∀ x, (f x).val + (g x).val ≠ 0) : ContinuousMap.Homotopy f g := by
  let chord (p : unitInterval × X) : Space :=
    (1 - p.1.val) • (f p.2).val + p.1.val • (g p.2).val
  have left (x : X) : ‖(f x).val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right]
    using (f x).property
  have right (x : X) : ‖(g x).val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right]
    using (g x).property
  have genuine (p : unitInterval × X) : chord p ≠ 0 := by
    rcases eq_or_lt_of_le p.1.property.1 with at_zero | after_zero
    · dsimp only [chord]
      rw [← at_zero, sub_zero, one_smul, zero_smul, add_zero]
      exact norm_ne_zero_iff.mp ((left p.2).trans_ne one_ne_zero)
    · rcases eq_or_lt_of_le p.1.property.2 with at_one | before_one
      · dsimp only [chord]
        rw [at_one, sub_self, zero_smul, one_smul, zero_add]
        exact norm_ne_zero_iff.mp ((right p.2).trans_ne one_ne_zero)
      · exact minorArc_chord_ne_zero (left p.2) (right p.2) (nonantipodal p.2)
          ⟨after_zero, before_one⟩
  have ct : Continuous fun p : unitInterval × X => p.1.val :=
    continuous_subtype_val.comp continuous_fst
  have cf : Continuous fun p : unitInterval × X => (f p.2).val :=
    continuous_subtype_val.comp (f.continuous.comp continuous_snd)
  have cg : Continuous fun p : unitInterval × X => (g p.2).val :=
    continuous_subtype_val.comp (g.continuous.comp continuous_snd)
  have cc : Continuous chord := ((continuous_const.sub ct).smul cf).add (ct.smul cg)
  let path (p : unitInterval × X) := NormedSpace.normalize (chord p)
  have cp : Continuous path := (cc.norm.inv₀ (fun p => norm_ne_zero_iff.mpr (genuine p))).smul cc
  have member (p : unitInterval × X) : path p ∈ Metric.sphere (0 : Space) 1 := by
    rw [Metric.mem_sphere, dist_zero_right]
    exact NormedSpace.norm_normalize (genuine p)
  refine ⟨⟨fun p => ⟨path p, member p⟩, cp.subtype_mk _⟩, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    simpa only [path, chord, Set.Icc.coe_zero, sub_zero, one_smul, zero_smul, add_zero]
      using NormedSpace.normalize_eq_self_of_norm_eq_one (left x)
  · intro x
    apply Subtype.ext
    simpa only [path, chord, Set.Icc.coe_one, sub_self, zero_smul, one_smul, zero_add]
      using NormedSpace.normalize_eq_self_of_norm_eq_one (right x)

end Unfoldings
