module

public import Unfoldings.Convex.FiniteNormalFanInterior
public import Unfoldings.Geometry.SpatialRotationSphere

/-! Voronoi labels and genericity for finite unit sites on the normal sphere. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeasureTheory SpatialRotation

variable {I : Type*} (site : I → Space)

/-- The unambiguous part of a Voronoi cell, considered as an open spatial cone. -/
def strictVoronoiCone (i : I) : Set Space := interior (finiteHullNormalCone site i)

/-- The spherical Voronoi walls include every tie between distinct maximizing sites. -/
def voronoiWalls : Set Space :=
  {x | x ∈ Metric.sphere 0 1 ∧
    ∃ i j, i ≠ j ∧ x ∈ finiteHullNormalCone site i ∧ x ∈ finiteHullNormalCone site j}

theorem strictVoronoiCone_isOpen (i : I) : IsOpen (strictVoronoiCone site i) := isOpen_interior

theorem strictVoronoiCone_pairwise_disjoint [Finite I] (injective : Function.Injective site) :
    Pairwise fun i j => Disjoint (strictVoronoiCone site i) (strictVoronoiCone site j) := by
  intro i j ne
  apply Set.disjoint_left.mpr
  intro x hi hj
  have first := (mem_interior_finiteHullNormalCone_iff injective i).mp hi j ne.symm
  have last := (mem_interior_finiteHullNormalCone_iff injective j).mp hj i ne
  exact (lt_irrefl _) (first.trans last)

/-- The open cones and walls cover the sphere, including higher-order ties. -/
theorem sphere_subset_strictVoronoiCone_union_walls [Finite I] [Nonempty I]
    (injective : Function.Injective site) :
    Metric.sphere 0 1 ⊆ (⋃ i, strictVoronoiCone site i) ∪ voronoiWalls site := by
  intro x hx
  have member : x ∈ ⋃ i, finiteHullNormalCone site i := by
    rw [iUnion_finiteHullNormalCone]
    trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
  by_cases strict : x ∈ strictVoronoiCone site i
  · exact Or.inl (Set.mem_iUnion.mpr ⟨i, strict⟩)
  · change x ∉ interior (finiteHullNormalCone site i) at strict
    rw [mem_interior_finiteHullNormalCone_iff injective i] at strict
    push Not at strict
    obtain ⟨j, ne, ties⟩ := strict
    have hj : x ∈ finiteHullNormalCone site j := fun k => (hi k).trans ties
    exact Or.inr ⟨hx, i, j, ne.symm, hi, hj⟩

/-- A Haar rotation gives every fixed point of a finite unit family a unique
Voronoi label almost surely. The rotation acts on the sites. -/
theorem ae_unique_strictVoronoiCone [Finite I] [Nonempty I] {V : Type*} [Finite V]
    (injective : Function.Injective site) (point : V → Space) (unit : ∀ v, ‖point v‖ = 1) :
    ∀ᵐ g ∂probability, ∀ v, ∃! i, point v ∈ strictVoronoiCone (fun j => linear g (site j)) i := by
  let pairs := {p : I × I // p.1 ≠ p.2}
  let normal (p : pairs) := innerSL ℝ (site p.val.1 - site p.val.2)
  have nonzero (p : pairs) : normal p ≠ 0 := by
    intro zero
    have h := DFunLike.congr_fun zero (site p.val.1 - site p.val.2)
    change inner ℝ (site p.val.1 - site p.val.2) (site p.val.1 - site p.val.2) = 0 at h
    exact p.property (injective (sub_eq_zero.mp (inner_self_eq_zero.mp h)))
  let regular (g : SpatialRotation) : Prop := ∀ v p, normal p (linear g (point v)) ≠ 0
  have generic' : ∀ᵐ g ∂probability, regular g :=
    ae_avoids_finite_hyperplanes point unit normal nonzero
  have inverse : MeasurePreserving (fun g : SpatialRotation => g⁻¹) probability probability :=
    Measure.measurePreserving_inv probability
  have inverse_regular : ∀ᵐ g ∂probability, ∀ v p, normal p (linear g⁻¹ (point v)) ≠ 0 := by
    exact inverse.quasiMeasurePreserving.ae (p := regular) generic'
  filter_upwards [inverse_regular] with g generic
  intro v
  have inj_rot : Function.Injective (fun j => linear g (site j)) :=
    (isometry g).injective.comp injective
  have onsphere : point v ∈ Metric.sphere (0 : Space) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using unit v
  rcases sphere_subset_strictVoronoiCone_union_walls (fun j => linear g (site j)) inj_rot
      onsphere with has_label | wall
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp has_label
    refine ⟨i, hi, ?_⟩
    intro j hj
    by_contra ne
    exact Set.disjoint_left.mp (strictVoronoiCone_pairwise_disjoint _ inj_rot ne) hj hi
  · obtain ⟨_, i, j, ne, hi, hj⟩ := wall
    have tie : inner ℝ (point v) (linear g (site i)) = inner ℝ (point v) (linear g (site j)) :=
      le_antisymm (hj i) (hi j)
    apply (generic v ⟨(i, j), ne⟩).elim
    change inner ℝ (site i - site j) (linear g⁻¹ (point v)) = 0
    rw [← inner_linear g, map_sub, linear_apply_inv, inner_sub_left, sub_eq_zero]
    simpa only [real_inner_comm (point v)] using tie

theorem image_finiteHullNormalCone (g : SpatialRotation) (i : I) :
    linear g '' finiteHullNormalCone site i =
      finiteHullNormalCone (fun j => linear g (site j)) i := by
  ext n
  constructor
  · rintro ⟨m, hm, rfl⟩ j
    change inner ℝ (linear g m) (linear g (site j)) ≤ inner ℝ (linear g m) (linear g (site i))
    simpa only [inner_linear] using hm j
  · intro hn
    refine ⟨linear g⁻¹ n, ?_, linear_apply_inv _ _⟩
    intro j
    change inner ℝ (linear g⁻¹ n) (site j) ≤ inner ℝ (linear g⁻¹ n) (site i)
    rw [← inner_linear g (linear g⁻¹ n) (site j),
      ← inner_linear g (linear g⁻¹ n) (site i), linear_apply_inv]
    exact hn j

theorem image_strictVoronoiCone (g : SpatialRotation) (i : I) :
    linear g '' strictVoronoiCone site i =
      strictVoronoiCone (fun j => linear g (site j)) i := by
  rw [strictVoronoiCone, strictVoronoiCone]
  have maps : linear g '' interior (finiteHullNormalCone site i) =
      interior (linear g '' finiteHullNormalCone site i) :=
    (isometry g).toHomeomorph.image_interior _
  rw [maps, image_finiteHullNormalCone]

theorem image_voronoiWalls (g : SpatialRotation) :
    linear g '' voronoiWalls site = voronoiWalls (fun j => linear g (site j)) := by
  have map_sphere {n : Space} (unit : n ∈ Metric.sphere (0 : Space) 1) :
      linear g n ∈ Metric.sphere (0 : Space) 1 := by
    rw [Metric.mem_sphere, dist_zero_right] at unit ⊢
    exact ((isometry g).norm_map n).trans unit
  have move {n : Space} (i : I) :
      linear g n ∈ finiteHullNormalCone (fun j => linear g (site j)) i ↔
        n ∈ finiteHullNormalCone site i := by
    rw [← image_finiteHullNormalCone]
    exact (isometry g).injective.mem_set_image
  ext n
  constructor
  · rintro ⟨m, ⟨unit, i, j, ne, hi, hj⟩, rfl⟩
    exact ⟨map_sphere unit, i, j, ne, (move i).mpr hi, (move j).mpr hj⟩
  · rintro ⟨unit, i, j, ne, hi, hj⟩
    let m := linear g⁻¹ n
    have image : linear g m = n := linear_apply_inv _ _
    rw [← image] at hi hj
    have m_unit : m ∈ Metric.sphere (0 : Space) 1 := by
      rw [Metric.mem_sphere, dist_zero_right] at unit ⊢
      exact ((isometry g⁻¹).norm_map n).trans unit
    exact ⟨m, ⟨m_unit, i, j, ne, (move i).mp hi, (move j).mp hj⟩, image⟩

end Unfoldings.FewestNets
