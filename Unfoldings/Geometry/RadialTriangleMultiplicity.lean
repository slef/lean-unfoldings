module

public import Unfoldings.Geometry.RadialTriangleCoverage
public import Mathlib.Topology.LocallyConstant.Basic

/-! An exact pairing of radial edges preserves multiplicity across every nonvertex point. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Module
open scoped Topology

/-- The weight of a triangle at a nonvertex point, doubled so an open edge
has integer weight one. -/
def radialTriangleWeight (b : Basis (Fin 3) ℝ Space) (p : Space) : ℕ :=
  if ∀ i, 0 < b.coord i p then 2 else if ∀ i, 0 ≤ b.coord i p then 1 else 0

/-- A point of the open radial edge opposite vertex `e`. -/
def OnOpenRadialEdge (b : Basis (Fin 3) ℝ Space) (e : Fin 3) (p : Space) : Prop :=
  b.coord e p = 0 ∧ ∀ i ≠ e, 0 < b.coord i p

private theorem radialTriangleWeight_eventually_eq_of_not_on_edge
    (b : Basis (Fin 3) ℝ Space) {p : Space} (unit : ‖p‖ = 1) (sites : ∀ i, ‖b i‖ = 1)
    (not_vertex : ∀ i, p ≠ b i) (not_edge : ∀ e, ¬ OnOpenRadialEdge b e p) :
    ∀ᶠ q in 𝓝 p, radialTriangleWeight b q = radialTriangleWeight b p := by
  classical
  by_cases inside : ∀ i, 0 < b.coord i p
  · have positive (i : Fin 3) : ∀ᶠ q in 𝓝 p, 0 < b.coord i q :=
      (isOpen_lt continuous_const (b.coord i).continuous_of_finiteDimensional).mem_nhds (inside i)
    filter_upwards [Filter.eventually_all.mpr positive] with q hq
    simp only [radialTriangleWeight, ite_eq_left inside, ite_eq_left hq]
  have outside : ∃ j, b.coord j p < 0 := by
    by_contra! all
    push Not at inside
    obtain ⟨e, h_e⟩ := inside
    have at_e : b.coord e p = 0 := le_antisymm h_e (all e)
    have other_pos (j : Fin 3) (different : j ≠ e) : 0 < b.coord j p := by
      by_contra! h_j
      have at_j : b.coord j p = 0 := le_antisymm h_j (all j)
      obtain ⟨k, h_ke, h_kj⟩ : ∃ k : Fin 3, k ≠ e ∧ k ≠ j := by
        have hcard : ({e, j} : Finset (Fin 3)).card = 2 := by simp [different.symm]
        obtain ⟨k, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
          (t := Finset.univ) (s := {e, j}) (by simp [hcard])
        exact ⟨k, by simpa using hk⟩
      apply not_vertex k
      apply eq_triangle_vertex_of_single_coord b sites unit (all k)
      intro i hi
      by_cases equal : i = e
      · rwa [equal]
      by_cases equal' : i = j
      · rwa [equal']
      exfalso
      omega
    exact not_edge e ⟨at_e, other_pos⟩
  obtain ⟨j, hj⟩ := outside
  have near : ∀ᶠ q in 𝓝 p, b.coord j q < 0 :=
    (isOpen_lt (b.coord j).continuous_of_finiteDimensional continuous_const).mem_nhds hj
  filter_upwards [near] with q hq
  have nq : ¬ ∀ i, 0 ≤ b.coord i q := fun witness => hq.not_ge (witness j)
  have np : ¬ ∀ i, 0 ≤ b.coord i p := fun witness => hj.not_ge (witness j)
  simp only [radialTriangleWeight, ite_eq_right inside, ite_eq_right np, ite_eq_right nq,
    ite_eq_right (fun h : ∀ i, 0 < b.coord i q => nq (fun i => (h i).le))]

/-- At a strict shared edge the two weights together are locally two, including
points on the edge itself. -/
theorem radialTriangleWeight_pair_eventually_eq {b c : Basis (Fin 3) ℝ Space}
    {e f : Fin 3} {p : Space} (left : OnOpenRadialEdge b e p) (right : OnOpenRadialEdge c f p)
    {scale : ℝ} (opposite : scale < 0) (transverse : ∀ q, b.coord e q = scale * c.coord f q) :
    ∀ᶠ q in 𝓝 p, radialTriangleWeight b q + radialTriangleWeight c q = 2 := by
  classical
  have keep (d : Basis (Fin 3) ℝ Space) (edge : Fin 3) (h : OnOpenRadialEdge d edge p) :
      ∀ᶠ q in 𝓝 p, ∀ i ≠ edge, 0 < d.coord i q := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases same : i = edge
    · simp [same]
    · have near : ∀ᶠ q in 𝓝 p, 0 < d.coord i q :=
        (isOpen_lt continuous_const (d.coord i).continuous_of_finiteDimensional).mem_nhds
          (h.2 i same)
      exact near.mono (fun _ value _ => value)
  filter_upwards [keep b e left, keep c f right] with q first last
  have weight (d : Basis (Fin 3) ℝ Space) (i : Fin 3) (others : ∀ j ≠ i, 0 < d.coord j q) :
      radialTriangleWeight d q = if 0 < d.coord i q then 2 else if 0 ≤ d.coord i q then 1 else 0 := by
    have strict : (∀ j, 0 < d.coord j q) ↔ 0 < d.coord i q := by
      refine ⟨fun h => h i, fun h j => ?_⟩
      by_cases same : j = i
      · simpa only [same] using h
      · exact others j same
    have weak : (∀ j, 0 ≤ d.coord j q) ↔ 0 ≤ d.coord i q := by
      refine ⟨fun h => h i, fun h j => ?_⟩
      by_cases same : j = i
      · simpa only [same] using h
      · exact (others j same).le
    simp only [radialTriangleWeight, strict, weak]
  rw [weight b e first, weight c f last, transverse]
  rcases lt_trichotomy (c.coord f q) 0 with negative | zero | positive
  · have sign := mul_pos_of_neg_of_neg opposite negative
    simp only [ite_eq_left sign, ite_eq_right negative.not_ge, ite_eq_right negative.not_gt,
      add_zero]
  · simp only [zero, mul_zero, lt_self_iff_false, ite_false, le_refl, ite_true]
  · have sign := mul_neg_of_neg_of_pos opposite positive
    simp only [ite_eq_left positive, ite_eq_right sign.not_ge, ite_eq_right sign.not_gt, zero_add]

/-- Sharing an edge is an involution on the named incident sides. These local
pairings make the total weight locally constant on the punctured sphere. -/
theorem eventually_radialTriangleWeight_sum_eq {I : Type*} [Fintype I]
    (b : I → Basis (Fin 3) ℝ Space) (sites : ∀ i j, ‖b i j‖ = 1)
    (mate : I × Fin 3 → I × Fin 3) (involutive : Function.Involutive mate)
    (preserves_edge : ∀ e p, OnOpenRadialEdge (b e.1) e.2 p →
      OnOpenRadialEdge (b (mate e).1) (mate e).2 p)
    (opposite : ∀ e, ∃ c < (0 : ℝ), ∀ q,
      (b e.1).coord e.2 q = c * (b (mate e).1).coord (mate e).2 q)
    {p : Space} (unit : ‖p‖ = 1) (not_vertex : ∀ i j, p ≠ b i j) :
    ∀ᶠ q in 𝓝 p, (∑ i, radialTriangleWeight (b i) q) = ∑ i, radialTriangleWeight (b i) p := by
  classical
  let A (i : I) := ∃ e, OnOpenRadialEdge (b i) e p
  let edge (i : I) (h : A i) := Classical.choose h
  have at_edge (i : I) (h : A i) : OnOpenRadialEdge (b i) (edge i h) p :=
    Classical.choose_spec h
  have unique (i : I) {e f : Fin 3} (he : OnOpenRadialEdge (b i) e p)
      (hf : OnOpenRadialEdge (b i) f p) : e = f := by
    by_contra different
    exact (he.2 f (Ne.symm different)).ne' hf.1
  let partner (i : I) := if h : A i then (mate (i, edge i h)).1 else i
  have swap_twice : Function.Involutive partner := by
    intro i
    by_cases h : A i
    · rw [show partner i = (mate (i, edge i h)).1 from dite_eq_left h]
      let f := mate (i, edge i h)
      have paired := preserves_edge (i, edge i h) p (at_edge i h)
      have h' : A f.1 := ⟨f.2, paired⟩
      rw [show partner f.1 = (mate (f.1, edge f.1 h')).1 from dite_eq_left h',
        unique f.1 (at_edge f.1 h') paired]
      change (mate f).1 = i
      exact congrArg Prod.fst (involutive (i, edge i h))
    · have fixed : partner i = i := dite_eq_right h
      rw [fixed, fixed]
  let permutation := swap_twice.toPerm
  let w (q : Space) (i : I) := radialTriangleWeight (b i) q
  have weight_at_edge (i : I) (e : Fin 3) (h : OnOpenRadialEdge (b i) e p) :
      w p i = 1 := by
    unfold w radialTriangleWeight
    rw [ite_eq_right (fun positive : ∀ j, 0 < (b i).coord j p => (positive e).ne' h.1)]
    apply ite_eq_left
    intro j
    by_cases same : j = e
    · rw [same, h.1]
    · exact (h.2 j same).le
  have locally (i : I) :
      ∀ᶠ q in 𝓝 p, w q i + w q (partner i) = w p i + w p (partner i) := by
    by_cases h : A i
    · let e := edge i h
      let f := mate (i, e)
      have he := at_edge i h
      have hf := preserves_edge (i, e) p he
      have paired : partner i = f.1 := dite_eq_left h
      rw [paired, weight_at_edge i e he, weight_at_edge f.1 f.2 hf]
      obtain ⟨c, negative, scaled⟩ := opposite (i, e)
      exact radialTriangleWeight_pair_eventually_eq he hf negative scaled
    · have no_edge (e : Fin 3) : ¬ OnOpenRadialEdge (b i) e p := fun he => h ⟨e, he⟩
      have one := radialTriangleWeight_eventually_eq_of_not_on_edge (b i) unit
        (sites i) (not_vertex i) no_edge
      filter_upwards [one] with q same
      rw [show partner i = i from dite_eq_right h]
      exact congrArg (fun x : ℕ => x + x) same
  filter_upwards [Filter.eventually_all.mpr locally] with q hq
  have equal := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hq i)
  simp only [Finset.sum_add_distrib] at equal
  have permute (x : Space) : ∑ i, w x (partner i) = ∑ i, w x i :=
    Equiv.sum_comp permutation (w x)
  rw [permute, permute] at equal
  change (∑ i, w q i) = ∑ i, w p i
  omega

local notation "Sphere" => Subtype (fun p : Space => p ∈ Metric.sphere (0 : Space) 1)

/-- The total signed-edge count is the same at any two nonvertex sphere points. -/
theorem radialTriangleWeight_sum_eq {I : Type*} [Fintype I] [Nonempty I]
    (b : I → Basis (Fin 3) ℝ Space) (sites : ∀ i j, ‖b i j‖ = 1)
    (mate : I × Fin 3 → I × Fin 3) (involutive : Function.Involutive mate)
    (preserves_edge : ∀ e p, OnOpenRadialEdge (b e.1) e.2 p →
      OnOpenRadialEdge (b (mate e).1) (mate e).2 p)
    (opposite : ∀ e, ∃ c < (0 : ℝ), ∀ q,
      (b e.1).coord e.2 q = c * (b (mate e).1).coord (mate e).2 q)
    (x y : Sphere) (hx : ∀ i j, x.val ≠ b i j) (hy : ∀ i j, y.val ≠ b i j) :
    (∑ i, radialTriangleWeight (b i) x.val) = ∑ i, radialTriangleWeight (b i) y.val := by
  let vertex (ij : I × Fin 3) : Sphere :=
    ⟨b ij.1 ij.2, Metric.mem_sphere.mpr ((dist_zero_right _).trans (sites ij.1 ij.2))⟩
  let vertices := Set.range vertex
  let X := (verticesᶜ : Set Sphere)
  let : PreconnectedSpace X := Subtype.preconnectedSpace
    (unitSphere_isPathConnected_compl_finite (Set.finite_range vertex)
      (Set.range_nonempty vertex)).isConnected.isPreconnected
  let point (z : X) : Space := z.val.val
  have continuous : Continuous point := continuous_subtype_val.comp continuous_subtype_val
  let μ (z : X) : ℕ := ∑ i, radialTriangleWeight (b i) (point z)
  have local_const : IsLocallyConstant μ := (IsLocallyConstant.iff_eventually_eq μ).mpr (fun z => by
    have unit : ‖point z‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using z.val.property
    have avoid (i : I) (j : Fin 3) : point z ≠ b i j :=
      fun equal => z.property ⟨(i, j), Subtype.ext equal.symm⟩
    exact continuous.continuousAt.eventually
      (eventually_radialTriangleWeight_sum_eq b sites mate involutive preserves_edge opposite unit avoid))
  have hx' : x ∈ X := fun ⟨⟨i, j⟩, equal⟩ => hx i j (congrArg Subtype.val equal).symm
  have hy' : y ∈ X := fun ⟨⟨i, j⟩, equal⟩ => hy i j (congrArg Subtype.val equal).symm
  exact local_const.apply_eq_of_preconnectedSpace ⟨x, hx'⟩ ⟨y, hy'⟩

end Unfoldings
