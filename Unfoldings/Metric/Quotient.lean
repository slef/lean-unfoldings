module

public import Unfoldings.Metric.Gluing
public import Mathlib.Logic.Relation
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Declared seam equivalence and the metric quotient

The seam quotient identifies exactly finite chains of declared seams. Its
topology comes from the disjoint union of the original cells, independently of
the route pseudometric. There is a continuous surjection to the metric
realization. Exactness means that this map is injective.

Finite families of compact cells have compact, complete metric realizations
even before exactness is proved. Once exactness is established, the seam
quotient and the metric realization are homeomorphic.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

universe u v

variable {ι : Type u} (E : ι → Type v) [∀ i, PseudoEMetricSpace (E i)]

/-- The quotient by finite seam chains, with the quotient topology of the cells. -/
abbrev SeamQuotient (glue : Total E → Total E → Prop) := Quot glue

/-- A tagged point in the quotient by declared identifications alone. -/
def seamPoint (glue : Total E → Total E → Prop) (x : Total E) : SeamQuotient E glue :=
  Quot.mk glue x

omit [∀ i, PseudoEMetricSpace (E i)] in
@[simp] theorem seamPoint_eq_iff (glue : Total E → Total E → Prop) (x y : Total E) :
    seamPoint E glue x = seamPoint E glue y ↔ Relation.EqvGen glue x y :=
  ⟨Quot.eqvGen_exact, Quot.eqvGen_sound⟩

/-- Declared seam chains always have zero route distance. -/
theorem point_eq_of_eqvGen {glue : Total E → Total E → Prop} {x y : Total E}
    (related : Relation.EqvGen glue x y) : point E glue x = point E glue y := by
  induction related with
  | rel a b h => exact point_eq_of_glue E h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ hab hbc => exact hab.trans hbc

/-- The metric construction makes no identifications beyond finite seam chains. -/
def Exact (glue : Total E → Total E → Prop) : Prop :=
  ∀ x y, point E glue x = point E glue y → Relation.EqvGen glue x y

theorem point_eq_iff_of_exact {glue : Total E → Total E → Prop} (exact : Exact E glue)
    (x y : Total E) : point E glue x = point E glue y ↔ Relation.EqvGen glue x y :=
  ⟨exact x y, point_eq_of_eqvGen E⟩

/-- The map from declared seam classes to metric points may identify further classes. -/
def toMetric (glue : Total E → Total E → Prop) : SeamQuotient E glue → Realization E glue :=
  Quot.lift (point E glue) (fun _ _ h => point_eq_of_glue E h)

@[simp] theorem toMetric_seamPoint (glue : Total E → Total E → Prop) (x : Total E) :
    toMetric E glue (seamPoint E glue x) = point E glue x := rfl

theorem point_surjective (glue : Total E → Total E → Prop) :
    Function.Surjective (point E glue) := by
  intro p
  obtain ⟨x, rfl⟩ := @SeparationQuotient.surjective_mk (PreSpace E glue) _ p
  exact ⟨x, rfl⟩

theorem toMetric_surjective (glue : Total E → Total E → Prop) :
    Function.Surjective (toMetric E glue) := by
  intro p
  obtain ⟨x, rfl⟩ := point_surjective E glue p
  exact ⟨seamPoint E glue x, rfl⟩

theorem exact_iff_toMetric_injective (glue : Total E → Total E → Prop) :
    Exact E glue ↔ Function.Injective (toMetric E glue) := by
  constructor
  · intro exact a b
    induction a using Quot.inductionOn with | h a =>
      induction b using Quot.inductionOn with | h b =>
        intro equal
        exact Quot.eqvGen_sound (exact a b equal)
  · intro injective x y equal
    exact Quot.eqvGen_exact (injective (a₁ := seamPoint E glue x)
      (a₂ := seamPoint E glue y) equal)

/-- Compatible nonexpanding coordinates that separate seam classes prove exactness. -/
theorem exact_of_separating_maps {κ Y : Type*} [EMetricSpace Y]
    (glue : Total E → Total E → Prop) (f : κ → ∀ i, E i → Y)
    (nonexpanding : ∀ k i, LipschitzWith 1 (f k i))
    (compatible : ∀ k x y, glue x y → f k x.1 x.2 = f k y.1 y.2)
    (separates : ∀ x y, (∀ k, f k x.1 x.2 = f k y.1 y.2) → Relation.EqvGen glue x y) :
    Exact E glue := by
  intro x y equal
  apply separates x y
  intro k
  exact congrArg (lift E glue (f k) (nonexpanding k) (compatible k)) equal

/-- Continuity uses the original disjoint-union topology, not the route topology. -/
theorem continuous_point (glue : Total E → Total E → Prop) : Continuous (point E glue) :=
  continuous_sigma (fun i => (of_lipschitz E glue i).continuous)

theorem continuous_toMetric (glue : Total E → Total E → Prop) :
    Continuous (toMetric E glue) :=
  continuous_quot_lift _ (continuous_point E glue)

instance [Finite ι] [∀ i, CompactSpace (E i)] (glue : Total E → Total E → Prop) :
    CompactSpace (Realization E glue) :=
  (point_surjective E glue).compactSpace (continuous_point E glue)

/-- The metric topology is a quotient of the original cells, possibly by extra equalities. -/
theorem isQuotientMap_point [Finite ι] [∀ i, CompactSpace (E i)]
    (glue : Total E → Total E → Prop) : Topology.IsQuotientMap (point E glue) :=
  .of_surjective_continuous (point_surjective E glue) (continuous_point E glue)

/-- Compactness gives completeness without any assumption about exactness. -/
theorem completeSpace_realization [Finite ι] [∀ i, CompactSpace (E i)]
    (glue : Total E → Total E → Prop) : CompleteSpace (Realization E glue) := inferInstance

/-- For compact finite gluing, exactness also identifies the two topologies. -/
def seamHomeomorph [Finite ι] [∀ i, CompactSpace (E i)]
    (glue : Total E → Total E → Prop) (exact : Exact E glue) :
    SeamQuotient E glue ≃ₜ Realization E glue :=
  Equiv.toHomeomorphOfContinuousClosed (Equiv.ofBijective (toMetric E glue)
    ⟨(exact_iff_toMetric_injective E glue).mp exact, toMetric_surjective E glue⟩)
    (continuous_toMetric E glue) (continuous_toMetric E glue).isClosedMap

@[simp] theorem seamHomeomorph_seamPoint [Finite ι] [∀ i, CompactSpace (E i)]
    (glue : Total E → Total E → Prop) (exact : Exact E glue) (x : Total E) :
    seamHomeomorph E glue exact (seamPoint E glue x) = point E glue x := rfl

end Unfoldings.MetricGluing
