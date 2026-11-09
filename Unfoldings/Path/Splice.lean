module

public import Unfoldings.Path.MetricGeodesic
public import Unfoldings.Geometry.ConvexCover
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Splicing an alternative shortest prefix into an actual geodesic

Normalize the replacement prefix to the original speed. Its constant extension
and the unchanged tail have the same Lipschitz bound and agree at the join.
A finite closed cover proves the global speed bound; unchanged endpoints then
force the spliced path to remain a geodesic.
-/

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace Path

variable {X : Type*} [MetricSpace X] {a b : X} {p : Path a b}

theorem IsGeodesic.lipschitzWith (geodesic : p.IsGeodesic) :
    LipschitzWith (nndist a b) p :=
  LipschitzWith.of_dist_le_mul (fun s t => (geodesic.dist_eq s t).le)

theorem extend_lipschitzWith {K : ℝ≥0} (speed : LipschitzWith K p) :
    LipschitzWith K p.extend := by
  have bound := speed.comp (LipschitzWith.projIcc (a := (0 : ℝ)) (b := 1) zero_le_one)
  have equal : (p.extend : ℝ → X) = p ∘ Set.projIcc 0 1 zero_le_one := rfl
  rw [equal]
  simpa only [mul_one] using bound

theorem IsGeodesic.exists_splice_prefix (geodesic : p.IsGeodesic)
    (t : unitInterval) (positive : 0 < t) (q : Path a (p t)) (other : q.IsGeodesic) :
    ∃ r : Path a b, r.IsGeodesic ∧
      (∀ u ≤ t, r u = q.extend ((u : ℝ) / (t : ℝ))) ∧
      (∀ u, t ≤ u → r u = p u) := by
  have tpos : 0 < (t : ℝ) := positive
  let left (u : unitInterval) := q.extend ((u : ℝ) / (t : ℝ))
  have left_speed : LipschitzWith (nndist a b) left := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have bound := (extend_lipschitzWith other.lipschitzWith).dist_le_mul
      ((u : ℝ) / (t : ℝ)) ((v : ℝ) / (t : ℝ))
    change dist (left u) (left v) ≤ dist a (p t) *
      dist ((u : ℝ) / (t : ℝ)) ((v : ℝ) / (t : ℝ)) at bound
    rw [geodesic.dist_source, Real.dist_eq, ← sub_div, abs_div, abs_of_pos tpos] at bound
    apply bound.trans_eq
    change (dist a b * (t : ℝ)) * (|(u : ℝ) - (v : ℝ)| / (t : ℝ)) =
      dist a b * dist u v
    rw [Subtype.dist_eq, Real.dist_eq]
    field_simp
  have joined : left t = p t := by
    dsimp only [left]
    rw [div_self tpos.ne', q.extend_one]
  let f (u : unitInterval) := if u ≤ t then left u else p u
  have before (u : unitInterval) (hu : u ≤ t) : f u = left u := ite_eq_left hu
  have after (u : unitInterval) (hu : t ≤ u) : f u = p u := by
    by_cases h : u ≤ t
    · have equal : u = t := le_antisymm h hu
      subst u
      exact (before t le_rfl).trans joined
    · exact ite_eq_right h
  let pieces (i : Fin 2) : Set unitInterval :=
    if i = 0 then {u | u ≤ t} else {u | t ≤ u}
  have closed (i : Fin 2) : IsClosed (pieces i) := by
    fin_cases i
    · exact isClosed_Iic
    · exact isClosed_Ici
  have cover : ⋃ i, pieces i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro u
    rcases le_total u t with first | last
    · exact Set.mem_iUnion.mpr ⟨0, first⟩
    · exact Set.mem_iUnion.mpr ⟨1, last⟩
  have bounded (i : Fin 2) : LipschitzOnWith (nndist a b) f (pieces i) := by
    fin_cases i
    · intro u hu v hv
      rw [before u hu, before v hv]
      exact left_speed u v
    · intro u hu v hv
      rw [after u hu, after v hv]
      exact geodesic.lipschitzWith u v
  have speed : LipschitzWith (nndist a b) f :=
    Unfoldings.convex_subtype_lipschitzWith_of_finite_closed_cover
      (Set.Icc (0 : ℝ) 1) (convex_Icc _ _) pieces closed cover f (nndist a b) bounded
  let r : Path a b :=
    { toFun := f
      continuous_toFun := speed.continuous
      source' := by
        rw [before 0 t.property.1]
        change q.extend ((0 : ℝ) / (t : ℝ)) = a
        rw [zero_div, q.extend_zero]
      target' := (after 1 t.property.2).trans p.target }
  exact ⟨r, r.isGeodesic_of_lipschitz speed, before, after⟩

end Path
