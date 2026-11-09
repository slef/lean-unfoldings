module

public import Unfoldings.Metric.Quotient
public import Mathlib.Topology.Instances.Real.Lemmas

/-! Checks on the constructed metric: recovery, disconnectedness, and shortcuts. -/

@[expose] public section

open scoped ENNReal

namespace Unfoldings.Examples

/-- An unglued single cell retains exactly its original metric. -/
theorem single_cell_edist {X : Type*} [PseudoEMetricSpace X] (x y : X) :
    edist (MetricGluing.of (fun _ : Unit => X) (fun _ _ => False) () x)
      (MetricGluing.of (fun _ : Unit => X) (fun _ _ => False) () y) = edist x y := by
  apply le_antisymm (MetricGluing.edist_of_le (fun _ : Unit => X) (fun _ _ => False) () x y)
  exact MetricGluing.map_edist_le (fun _ : Unit => X) (fun _ _ => False)
    (fun _ z => z) (fun _ => LipschitzWith.id) (by intro _ _ h; exact h.elim) ⟨(), x⟩ ⟨(), y⟩

/-- Distinct cells with no declared seams are infinitely far apart. -/
theorem disconnected_cells_edist {ι : Type*} (E : ι → Type*) [∀ i, PseudoEMetricSpace (E i)]
    {i j : ι} (different : i ≠ j) (x : E i) (y : E j) :
    edist (MetricGluing.of E (fun _ _ => False) i x)
      (MetricGluing.of E (fun _ _ => False) j y) = ⊤ := by
  classical
  let d : MetricGluing.Total E → MetricGluing.Total E → ℝ≥0∞ :=
    fun a b => if a.1 = b.1 then 0 else ⊤
  have self (a : MetricGluing.Total E) : d a a = 0 := by simp [d]
  have triangle (a b c : MetricGluing.Total E) : d a c ≤ d a b + d b c := by
    by_cases ac : a.1 = c.1
    · simp [d, ac]
    · by_cases ab : a.1 = b.1
      · have bc : b.1 ≠ c.1 := fun h => ac (ab.trans h)
        simp [d, ab, bc]
      · simp [d, ac, ab]
  have bound (a b : MetricGluing.Total E) :
      d a b ≤ MetricGluing.stepCost E (fun _ _ => False) a b := by
    obtain ⟨k, a⟩ := a
    obtain ⟨l, b⟩ := b
    by_cases same : k = l
    · subst l
      simp [d, MetricGluing.stepCost, MetricGluing.faceCost]
    · simp [d, MetricGluing.stepCost, MetricGluing.faceCost, same]
  change Route.distance (MetricGluing.stepCost E (fun _ _ => False)) ⟨i, x⟩ ⟨j, y⟩ = ⊤
  apply top_unique
  have lower := Route.le_distance (MetricGluing.stepCost E (fun _ _ => False)) d self triangle bound
    ⟨i, x⟩ ⟨j, y⟩
  simpa [d, different] using lower

/-- Even a single cell can lose global injectivity when two of its points are identified. -/
theorem endpoint_identification :
    MetricGluing.of (fun _ : Unit => ℝ)
        (fun a b => a.2 = 0 ∧ b.2 = 1) () 0 =
      MetricGluing.of (fun _ : Unit => ℝ)
        (fun a b => a.2 = 0 ∧ b.2 = 1) () 1 :=
  MetricGluing.point_eq_of_glue _ ⟨rfl, rfl⟩

/-- Identify all nonzero real points with one another, while leaving zero unpaired. -/
def puncturedGlue (a b : MetricGluing.Total (fun _ : Unit => ℝ)) : Prop :=
  a.2 ≠ 0 ∧ b.2 ≠ 0

/-- Declared seam chains in this example still keep zero separate from one. -/
theorem puncturedGlue_not_related :
    ¬ Relation.EqvGen puncturedGlue ⟨(), 0⟩ ⟨(), 1⟩ := by
  have invariant {a b} (h : Relation.EqvGen puncturedGlue a b) :
      a.2 = 0 ↔ b.2 = 0 := by
    induction h with
    | rel a b h => simp [h.1, h.2]
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ hab hbc => exact hab.trans hbc
  intro h
  have impossible := (invariant h).mp rfl
  exact one_ne_zero impossible

/-- Continuity forces zero into the collapsed metric class despite the declared seams. -/
theorem puncturedGlue_metric_collapse :
    MetricGluing.of (fun _ : Unit => ℝ) puncturedGlue () 0 =
      MetricGluing.of (fun _ : Unit => ℝ) puncturedGlue () 1 := by
  let f := MetricGluing.of (fun _ : Unit => ℝ) puncturedGlue ()
  have agrees : Set.EqOn f (fun _ => f 1) (Set.Ioi 0) := by
    intro x hx
    exact MetricGluing.point_eq_of_glue _ ⟨ne_of_gt hx, one_ne_zero⟩
  have agrees' := agrees.closure
    (MetricGluing.of_lipschitz (fun _ : Unit => ℝ) puncturedGlue ()).continuous continuous_const
  exact agrees' (by simp [closure_Ioi])

/-- Exactness cannot be claimed for unrestricted gluing relations. -/
theorem puncturedGlue_not_exact : ¬ MetricGluing.Exact (fun _ : Unit => ℝ) puncturedGlue := by
  intro exact
  exact puncturedGlue_not_related (exact ⟨(), 0⟩ ⟨(), 1⟩ puncturedGlue_metric_collapse)

end Unfoldings.Examples
