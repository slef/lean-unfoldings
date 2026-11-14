module

public import Unfoldings.Basic
public import Unfoldings.Topology.FiniteCellCovering
public import Unfoldings.Metric.ConvexCover
public import Unfoldings.Metric.Quotient
public import Mathlib.Analysis.Convex.Contractible

/-! A locally homeomorphic development of finitely many complete cells is globally isometric. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

universe u v

variable {I : Type u} (E : I → Type v) [∀ i, EMetricSpace (E i)]
  (glue : Total E → Total E → Prop)
  (f : Realization E glue → Plane)
  (isometric : ∀ i, Isometry (f ∘ of E glue i))

include isometric in
theorem lipschitz_of_isometric_cells : LipschitzWith 1 f := by
  have compatible : ∀ a b, glue a b →
      f (of E glue a.1 a.2) = f (of E glue b.1 b.2) :=
    fun a b joined => congrArg f (point_eq_of_glue E joined)
  have equal := lift_unique E glue (fun i => f ∘ of E glue i)
    (fun i => (isometric i).lipschitzWith) compatible f (fun _ _ => rfl)
  rw [equal]
  exact lift_lipschitz E glue _ (fun i => (isometric i).lipschitzWith) compatible

variable [Finite I] [∀ i, CompleteSpace (E i)]
  [PreconnectedSpace (Realization E glue)] [Nonempty (Realization E glue)]

include isometric in
/-- Finite complete cells rule out additional sheets and metric shortcuts. -/
theorem isometry_of_localHomeomorph_isometric_cells (local_homeomorph : IsLocalHomeomorph f) :
    Isometry f := by
  have cover : ∀ x : Realization E glue, ∃ i, ∃ p : E i, of E glue i p = x := by
    intro x
    obtain ⟨⟨i, p⟩, equal⟩ := point_surjective E glue x
    exact ⟨i, p, equal⟩
  have covering := isCoveringMap_of_finite_complete_cells E (of E glue)
    (fun i => (of_lipschitz E glue i).continuous) cover f isometric local_homeomorph
  let H := coveringHomeomorphOfSimplyConnected covering
  let g : ↥(Set.univ : Set Plane) → Realization E glue := fun y => H.symm y.val
  let pieces (i : I) : Set (Set.univ : Set Plane) :=
    {y | y.val ∈ Set.range (f ∘ of E glue i)}
  have closed (i : I) : IsClosed (pieces i) :=
    (isometric i).isClosedEmbedding.isClosed_range.preimage continuous_subtype_val
  have pieces_cover : (⋃ i, pieces i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨i, p, equal⟩ := cover (H.symm y.val)
    apply Set.mem_iUnion.mpr
    refine ⟨i, p, ?_⟩
    exact (congrArg H equal).trans (H.apply_symm_apply y.val)
  have inverse_bound : LipschitzWith 1 g := by
    apply convex_subtype_emetric_lipschitzWith_of_finite_closed_cover Set.univ convex_univ
      pieces closed pieces_cover g 1
    intro i a ha b hb
    obtain ⟨p, hp⟩ := ha
    obtain ⟨q, hq⟩ := hb
    have at_a : g a = of E glue i p := by
      apply H.injective
      exact (H.apply_symm_apply a.val).trans hp.symm
    have at_b : g b = of E glue i q := by
      apply H.injective
      exact (H.apply_symm_apply b.val).trans hq.symm
    rw [at_a, at_b]
    simp only [ENNReal.coe_one, one_mul]
    calc
      edist (of E glue i p) (of E glue i q) ≤ edist p q := edist_of_le E glue i p q
      _ = edist a b := by
        rw [← (isometric i).edist_eq p q, hp, hq]
        rfl
  intro x y
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul] using
      (lipschitz_of_isometric_cells E glue f isometric).edist_le_mul x y
  · have reverse := inverse_bound.edist_le_mul ⟨f x, Set.mem_univ _⟩ ⟨f y, Set.mem_univ _⟩
    change edist (H.symm (H x)) (H.symm (H y)) ≤ (1 : ENNReal) * edist (f x) (f y) at reverse
    simpa only [H.symm_apply_apply, one_mul] using reverse

end Unfoldings.MetricGluing
