module

public import Unfoldings.Metric.ConvexLocalLipschitz
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Convex faces lift across an excised cut by extending their unique interior copies. -/

@[expose] public section

noncomputable section

open Set
open scoped NNReal ENNReal

namespace Unfoldings

variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [EMetricSpace X] [CompleteSpace X] [EMetricSpace Y]

/-- A closed convex patch lifts isometrically when its interior has unique lifts and
restoration is a whole-ball isometry at each of those lifts. -/
theorem exists_isometric_convex_patch_lift {s : Set E} (convex : Convex ℝ s)
    (full : (interior s).Nonempty) (restore : X → Y) (nonexpanding : LipschitzWith 1 restore)
    (place : s → Y) (isometric : Isometry place)
    (interior_lifts : ∀ x : interior s, ∃! z, restore z = place ⟨x.val, interior_subset x.property⟩)
    (local_restore : ∀ (x : interior s) (z : X),
      restore z = place ⟨x.val, interior_subset x.property⟩ →
      ∃ r > 0, ∃ A : Metric.eball z (ENNReal.ofReal r) ≃ᵢ
        Metric.eball (restore z) (ENNReal.ofReal r), ∀ w, (A w).val = restore w.val) :
    ∃ lift : s → X, Isometry lift ∧ ∀ x, restore (lift x) = place x := by
  let inc : interior s → s := Set.inclusion interior_subset
  have inc_isometric : Isometry inc := fun _ _ => rfl
  let liftInterior (x : interior s) : X := (interior_lifts x).choose
  have agrees (x : interior s) : restore (liftInterior x) = place (inc x) :=
    (interior_lifts x).choose_spec.1
  have unique (x : interior s) (z : X) (h : restore z = place (inc x)) :
      z = liftInterior x := (interior_lifts x).choose_spec.2 z h
  have lifts_lipschitz : LipschitzWith 1 liftInterior := by
    apply convex_subtype_emetric_lipschitzWith_of_local (interior s) convex.interior
    intro x
    obtain ⟨r, positive, A, restore_eq⟩ := local_restore x (liftInterior x) (agrees x)
    let B (y : Metric.ball x r) : Metric.eball (restore (liftInterior x)) (ENNReal.ofReal r) :=
      ⟨place (inc y.val), by
        change edist (place (inc y.val)) (restore (liftInterior x)) < ENNReal.ofReal r
        rw [agrees x, isometric.edist_eq, inc_isometric.edist_eq]
        change edist y.val x < ENNReal.ofReal r
        rw [edist_dist]
        exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg |>.mpr y.property⟩
    have preimage (y : Metric.ball x r) : (A.symm (B y)).val = liftInterior y.val := by
      apply unique
      exact (restore_eq (A.symm (B y))).symm.trans
        (congrArg Subtype.val (A.apply_symm_apply (B y)))
    refine ⟨r, positive, ?_⟩
    intro y hy z hz
    have equal := A.symm.isometry.edist_eq (B ⟨y, hy⟩) (B ⟨z, hz⟩)
    change edist (A.symm (B ⟨y, hy⟩)).val (A.symm (B ⟨z, hz⟩)).val =
      edist (place (inc y)) (place (inc z)) at equal
    rw [preimage, preimage, isometric.edist_eq, inc_isometric.edist_eq] at equal
    simpa only [ENNReal.coe_one, one_mul] using equal.le
  have lifts_isometric : Isometry liftInterior := by
    intro x y
    apply le_antisymm
    · simpa only [ENNReal.coe_one, one_mul] using lifts_lipschitz x y
    · have lower := nonexpanding (liftInterior x) (liftInterior y)
      rw [agrees, agrees, isometric.edist_eq, inc_isometric.edist_eq] at lower
      simpa only [ENNReal.coe_one, one_mul] using lower
  have dense : DenseRange inc := by
    apply (denseRange_inclusion_iff (show interior s ⊆ s from interior_subset)).mpr
    rw [convex.closure_interior_eq_closure_of_nonempty_interior full]
    exact subset_closure
  let inducing := inc_isometric.isUniformInducing
  let L := (inducing.isDenseInducing dense).extend liftInterior
  have cont : Continuous L :=
    (uniformContinuous_uniformly_extend inducing dense lifts_lipschitz.uniformContinuous).continuous
  have on_interior (x : interior s) : L (inc x) = liftInterior x :=
    uniformly_extend_of_ind inducing dense lifts_lipschitz.uniformContinuous x
  have lift_edist : (fun xy : s × s => edist (L xy.1) (L xy.2)) =
      fun xy => edist xy.1 xy.2 := by
    apply Continuous.ext_on (dense.prodMap dense)
      (continuous_edist.comp ((cont.comp continuous_fst).prodMk (cont.comp continuous_snd)))
      continuous_edist
    rintro _ ⟨⟨x, y⟩, rfl⟩
    change edist (L (inc x)) (L (inc y)) = edist (inc x) (inc y)
    rw [on_interior, on_interior, lifts_isometric.edist_eq, inc_isometric.edist_eq]
  refine ⟨L, fun x y => congrFun lift_edist (x, y), ?_⟩
  have h : restore ∘ L = place := by
    apply Continuous.ext_on dense (nonexpanding.continuous.comp cont) isometric.continuous
    rintro _ ⟨x, rfl⟩
    exact (congrArg restore (on_interior x)).trans (agrees x)
  exact congrFun h

end Unfoldings
