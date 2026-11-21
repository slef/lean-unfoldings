module

public import Unfoldings.FewestNets.NormalVoronoi
public import Unfoldings.Combinatorics.ComponentEulerAccounting
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Measurable normal labels and their bounded component charges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeasureTheory SpatialRotation
open scoped BigOperators

variable {I : Type*} [Finite I] [Nonempty I] (site : I → Space)

open Classical in
/-- The normal's unique strict Voronoi label, with a fixed default on ties. -/
def voronoiLabel (point : Space) (g : SpatialRotation) : I :=
  if h : ∃ i, point ∈ strictVoronoiCone (fun j => linear g (site j)) i then
    Classical.choose h else Classical.choice inferInstance

theorem voronoiLabel_eq_of_mem_strictVoronoiCone (injective : Function.Injective site)
    (point : Space) (g : SpatialRotation) (i : I)
    (inside : point ∈ strictVoronoiCone (fun j => linear g (site j)) i) :
    voronoiLabel site point g = i := by
  have nonempty : ∃ j, point ∈ strictVoronoiCone (fun k => linear g (site k)) j :=
    ⟨i, inside⟩
  rw [voronoiLabel, dite_eq_left nonempty]
  by_contra distinct
  exact Set.disjoint_left.mp
    (strictVoronoiCone_pairwise_disjoint _ ((isometry g).injective.comp injective) distinct)
    (Classical.choose_spec nonempty) inside

omit [Nonempty I] in
theorem isOpen_strictVoronoi_rotation_set (injective : Function.Injective site)
    (point : Space) (i : I) :
    IsOpen {g : SpatialRotation | point ∈ strictVoronoiCone (fun j => linear g (site j)) i} := by
  have sets :
      {g : SpatialRotation | point ∈ strictVoronoiCone (fun j => linear g (site j)) i} =
        ⋂ j : {j : I // j ≠ i},
          {g : SpatialRotation | inner ℝ point (linear g (site j.val)) <
            inner ℝ point (linear g (site i))} := by
    ext g
    have inj_rot : Function.Injective (fun j => linear g (site j)) :=
      (isometry g).injective.comp injective
    change point ∈ interior (finiteHullNormalCone (fun j => linear g (site j)) i) ↔ _
    rw [mem_interior_finiteHullNormalCone_iff inj_rot i]
    simp
  rw [sets]
  apply isOpen_iInter_of_finite
  intro j
  have cont (k : I) : Continuous (fun g : SpatialRotation => inner ℝ point (linear g (site k))) :=
    continuous_const.inner (SpatialRotation.continuous_apply.comp
      (continuous_id.prodMk continuous_const))
  exact isOpen_lt (cont j.val) (cont i)

open Classical in
theorem measurableSet_voronoiLabel_eq (injective : Function.Injective site)
    (point : Space) (i : I) : MeasurableSet {g | voronoiLabel site point g = i} := by
  let event (j : I) := {g : SpatialRotation |
    point ∈ strictVoronoiCone (fun j => linear g (site j)) j}
  let excluded := (⋃ j, event j)ᶜ
  let default : I := Classical.choice inferInstance
  have event_measurable (j : I) : MeasurableSet (event j) :=
    (isOpen_strictVoronoi_rotation_set site injective point j).measurableSet
  let : Fintype I := Fintype.ofFinite _
  have excluded_measurable : MeasurableSet excluded := (MeasurableSet.iUnion event_measurable).compl
  have fiber : {g | voronoiLabel site point g = i} =
      event i ∪ (if default = i then excluded else ∅) := by
    ext g
    by_cases present : ∃ j, point ∈ strictVoronoiCone (fun j => linear g (site j)) j
    · obtain ⟨j, h⟩ := present
      have recognized := voronoiLabel_eq_of_mem_strictVoronoiCone site injective point g j h
      have not_excluded : g ∉ excluded := fun he => he (Set.mem_iUnion.mpr ⟨j, h⟩)
      change (voronoiLabel site point g = i) ↔ g ∈ event i ∪ _
      rw [recognized]
      constructor
      · rintro rfl
        exact Or.inl h
      · rintro (inside | fallback)
        · exact recognized.symm.trans
            (voronoiLabel_eq_of_mem_strictVoronoiCone site injective point g i inside)
        · split at fallback
          · exact (not_excluded fallback).elim
          · exact False.elim fallback
    · have in_excluded : g ∈ excluded := by
        intro h
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
        exact present ⟨j, hj⟩
      have not_i : g ∉ event i := fun hi => present ⟨i, hi⟩
      change (voronoiLabel site point g = i) ↔ g ∈ event i ∪ _
      rw [voronoiLabel, dite_eq_right present]
      change default = i ↔ _
      simp only [Set.mem_union, not_i, false_or]
      split <;> simp [*]
  rw [fiber]
  exact (event_measurable i).union (by split <;> simp [excluded_measurable])

open Classical in
theorem measurableSet_voronoiLabel_ne (injective : Function.Injective site)
    (u v : Space) :
    MeasurableSet {g | voronoiLabel site u g ≠ voronoiLabel site v g} := by
  let : Fintype I := Fintype.ofFinite _
  have eq : {g | voronoiLabel site u g = voronoiLabel site v g} =
      ⋃ i, {g | voronoiLabel site u g = i} ∩ {g | voronoiLabel site v g = i} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun same => ⟨_, same, rfl⟩, fun ⟨_, a, b⟩ => a.trans b.symm⟩
  change MeasurableSet {g | voronoiLabel site u g = voronoiLabel site v g}ᶜ
  rw [eq]
  exact (MeasurableSet.iUnion fun i =>
    (measurableSet_voronoiLabel_eq site injective u i).inter
      (measurableSet_voronoiLabel_eq site injective v i)).compl

/-- A component charge for a finite side set is integrable whenever its
individual label-change events are measurable. -/
theorem integrable_componentCharge_of_measurable {E Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (edges : Finset E)
    (changed : Ω → E → Prop) [∀ g, DecidablePred (changed g)]
    (measurable : ∀ s ∈ edges, MeasurableSet {g | changed g s}) :
    Integrable (fun g => componentCharge (edges.filter (changed g)).card) μ := by
  classical
  let event (s : E) := {g | changed g s}
  let any := ⋃ s : ↥edges, event s.val
  have any_meas : MeasurableSet any :=
    MeasurableSet.iUnion fun s => measurable s.val s.property
  have measure_count : Integrable (fun g =>
      ∑ s ∈ edges, (event s).indicator (fun _ => (1 : ℝ)) g) μ :=
    integrable_finsetSum _ fun s hs => (integrable_const 1).indicator (measurable s hs)
  have integrable := (measure_count.div_const 2).sub
    ((integrable_const 1).indicator any_meas)
  have count_eq (g : Ω) : (∑ s ∈ edges, (event s).indicator (fun _ => (1 : ℝ)) g) =
      ((edges.filter (changed g)).card : ℝ) := by
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro s _
    by_cases changed_s : changed g s <;> simp [event, changed_s]
  have present (g : Ω) : g ∈ any ↔ (edges.filter (changed g)).card ≠ 0 := by
    rw [← Nat.pos_iff_ne_zero, Finset.card_pos]
    constructor
    · intro h
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp h
      exact ⟨s.val, Finset.mem_filter.mpr ⟨s.property, hs⟩⟩
    · rintro ⟨s, hs⟩
      obtain ⟨he, hc⟩ := Finset.mem_filter.mp hs
      exact Set.mem_iUnion.mpr ⟨⟨s, he⟩, hc⟩
  have incidence (g : Ω) : any.indicator (fun _ => (1 : ℝ)) g =
      if (edges.filter (changed g)).card = 0 then 0 else 1 := by
    by_cases zero : (edges.filter (changed g)).card = 0
    · have outside : g ∉ any := fun h => (present g).mp h zero
      simp [Set.indicator_of_notMem outside, zero]
    · simp [Set.indicator_of_mem ((present g).mpr zero), zero]
  convert integrable using 1
  funext g
  simp [componentCharge, count_eq, incidence]

end Unfoldings.FewestNets
