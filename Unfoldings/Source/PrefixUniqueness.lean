module

public import Unfoldings.Path.Splice
public import Unfoldings.Polyhedron.GeodesicRegularity
public import Unfoldings.Source.CutLocus

/-!
# Proper prefixes of actual convex-boundary geodesics are unique

Splice any alternative shortest prefix into the unchanged tail. Reversed
geodesic continuation forces the whole spliced path to be the original path,
so the alternative prefix was equal as well. This excludes nonunique endpoints
at proper interior times; exclusion from their closure needs a stability proof.
-/

@[expose] public section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem geodesics_eq_of_final_interval
    {a b c d : C.Realization Set.univ} {p : Path a b} {q : Path c d}
    (geodesic : p.IsGeodesic) (other : q.IsGeodesic) (distinct : a ≠ b)
    (final_agreement : ∃ ε : unitInterval, ε < 1 ∧ ∀ t, ε ≤ t → p t = q t) :
    ∀ t, p t = q t := by
  obtain ⟨ε, before_end, agrees⟩ := final_agreement
  let δ : unitInterval := ⟨1 - (ε : ℝ), by constructor <;> linarith [ε.property.1, ε.property.2]⟩
  have positive : (0 : unitInterval) < δ := sub_pos.mpr before_end
  have reverse_distinct : p 1 ≠ p 0 := by
    simpa only [Path.source, Path.target] using distinct.symm
  have initial : ∀ t ≤ δ, (p.subpath 1 0) t = (q.subpath 1 0) t := by
    intro t ht
    apply agrees
    change (ε : ℝ) ≤ AffineMap.lineMap (1 : ℝ) 0 (t : ℝ)
    have bound : (t : ℝ) ≤ 1 - (ε : ℝ) := ht
    rw [AffineMap.lineMap_apply_ring]
    linarith
  have all := P.geodesics_eq_of_initial_interval (geodesic.subpath 1 0) (other.subpath 1 0)
    reverse_distinct ⟨δ, positive, initial⟩
  intro t
  let u : unitInterval := ⟨1 - (t : ℝ), by constructor <;> linarith [t.property.1, t.property.2]⟩
  have parameter : Path.intervalParam 1 0 u = t := by
    apply Subtype.ext
    change AffineMap.lineMap (1 : ℝ) 0 (1 - (t : ℝ)) = (t : ℝ)
    rw [AffineMap.lineMap_apply_ring]
    ring
  have equal := all u
  change p (Path.intervalParam 1 0 u) = q (Path.intervalParam 1 0 u) at equal
  rwa [parameter] at equal

theorem geodesic_prefix_unique :
    letI := P.metricSpace
    ∀ {a b : C.Realization Set.univ} {p : Path a b}, p.IsGeodesic → a ≠ b →
      ∀ (t : unitInterval), 0 < t → t < 1 →
        ∀ (q : Path a (p t)), q.IsGeodesic →
          ∀ u, q u = p (Path.intervalParam 0 t u) := by
  let := P.metricSpace
  intro a b p geodesic distinct t positive before_end q other
  obtain ⟨r, shortest, before, after⟩ := geodesic.exists_splice_prefix t positive q other
  have whole := P.geodesics_eq_of_final_interval shortest geodesic distinct
    ⟨t, before_end, after⟩
  intro u
  let time := Path.intervalParam 0 t u
  have inside : time ≤ t := (Path.intervalParam_mem_Icc t.property.1 u).2
  have ratio : (time : ℝ) / (t : ℝ) = (u : ℝ) := by
    change AffineMap.lineMap (0 : ℝ) (t : ℝ) (u : ℝ) / (t : ℝ) = (u : ℝ)
    rw [AffineMap.lineMap_apply_ring]
    have nonzero : (t : ℝ) ≠ 0 := (show (0 : ℝ) < (t : ℝ) from positive).ne'
    field_simp
    ring
  have equal := before time inside
  rw [ratio, q.extend_extends' u] at equal
  exact equal.symm.trans (whole time)

theorem geodesic_proper_prefix_not_nonunique :
    letI := P.metricSpace
    ∀ {a b : C.Realization Set.univ} {p : Path a b}, p.IsGeodesic → a ≠ b →
      ∀ (t : unitInterval), 0 < t → t < 1 → p t ∉ nonuniqueSourcePoints a := by
  let := P.metricSpace
  intro a b p geodesic distinct t positive before_end nonunique
  obtain ⟨q, r, first, last, different⟩ := nonunique
  apply different
  ext u
  exact (P.geodesic_prefix_unique geodesic distinct t positive before_end q first u).trans
    (P.geodesic_prefix_unique geodesic distinct t positive before_end r last u).symm

end Unfoldings.SpatialFolding.ConvexBoundary
