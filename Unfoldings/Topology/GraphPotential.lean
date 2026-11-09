module

public import Unfoldings.Topology.GraphExtension
public import Unfoldings.Topology.GraphPoints
public import Unfoldings.Topology.ContractibleLift
public import Mathlib.Topology.Covering.FundamentalGroupCircle

/-!
# Edge potentials on contractible embedded graphs

Map one chosen edge once around the circle and every other edge to zero.
Contractibility lifts this map to the real line. The real lift gives vertex
values differing by one along the chosen edge and equal along all other edges.
This is the topological obstruction that will rule out graph cycles.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.FiniteEmbeddedGraph

variable {Vertex Edge X : Type*} [TopologicalSpace X] [T2Space X]
  (G : FiniteEmbeddedGraph Vertex Edge X)

theorem exists_edge_winding_map (selected : Edge) :
    ∃ F : C(G.carrier, AddCircle (1 : ℝ)),
      (∀ v, F (G.vertexPoint v) = 0) ∧
      ∀ e t, (e = selected → F (G.edgeInclusion e t) = ((t : ℝ) : AddCircle (1 : ℝ))) ∧
        (e ≠ selected → F (G.edgeInclusion e t) = 0) := by
  classical
  let winding : C(unitInterval, AddCircle (1 : ℝ)) :=
    ⟨fun t => ((t : ℝ) : AddCircle (1 : ℝ)),
      (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val⟩
  let edges (e : Edge) := if e = selected then winding else ContinuousMap.const unitInterval 0
  have winding_zero : winding 0 = 0 := rfl
  have winding_one : winding 1 = 0 := AddCircle.coe_period (1 : ℝ)
  have at_zero (e : Edge) : edges e 0 = 0 := by
    by_cases equal : e = selected <;> simp [edges, equal, winding_zero]
  have at_one (e : Edge) : edges e 1 = 0 := by
    by_cases equal : e = selected <;> simp [edges, equal, winding_one]
  obtain ⟨F, vertices, on_edges⟩ := G.exists_continuous_extension (fun _ => 0) edges at_zero at_one
  refine ⟨F, vertices, ?_⟩
  intro e t
  have equal := on_edges e t
  change F (G.edgeInclusion e t) = edges e t at equal
  constructor
  · intro same
    have chosen : edges e = winding := by simp [edges, same]
    rw [chosen] at equal
    exact equal
  · intro different
    have chosen : edges e = ContinuousMap.const unitInterval 0 := by simp [edges, different]
    rw [chosen] at equal
    exact equal

theorem exists_edge_potential [ContractibleSpace G.carrier] (selected : Edge) :
    ∃ value : Vertex → ℝ,
      value (G.right selected) = value (G.left selected) + 1 ∧
        ∀ e ≠ selected, value (G.left e) = value (G.right e) := by
  classical
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let quotient : ℝ → AddCircle (1 : ℝ) := (↑)
  have covering : IsCoveringMap quotient := AddCircle.isCoveringMap_coe (1 : ℝ)
  have onto : Function.Surjective quotient := by
    intro x
    exact ⟨(AddCircle.equivIco (1 : ℝ) 0 x : ℝ), AddCircle.coe_equivIco⟩
  obtain ⟨F, at_vertices, on_edges⟩ := G.exists_edge_winding_map selected
  obtain ⟨lift, lifts⟩ := exists_covering_lift_of_contractible quotient covering onto F
  let value (v : Vertex) := lift (G.vertexPoint v)
  have at_vertex (v : Vertex) : quotient (value v) = 0 :=
    (congrFun lifts (G.vertexPoint v)).trans (at_vertices v)
  have along (e : Edge) (t : unitInterval) : quotient (lift (G.edgeInclusion e t)) =
      if e = selected then ((t : ℝ) : AddCircle (1 : ℝ)) else 0 := by
    by_cases same : e = selected
    · simpa only [Function.comp_apply, same, ite_true] using
        (congrFun lifts (G.edgeInclusion e t)).trans ((on_edges e t).1 same)
    · simpa only [Function.comp_apply, ite_eq_right same] using
        (congrFun lifts (G.edgeInclusion e t)).trans ((on_edges e t).2 same)
  have sum_quotient (a b : ℝ) : quotient (a + b) = quotient a + quotient b :=
    AddCircle.coe_add (1 : ℝ) a b
  let original : C(unitInterval, ℝ) := lift.comp (G.edgeInclusion selected)
  let linear : C(unitInterval, ℝ) := ⟨fun t => value (G.left selected) + (t : ℝ),
    continuous_const.add continuous_subtype_val⟩
  have same_quotient : quotient ∘ original = quotient ∘ linear := by
    funext t
    have first := along selected t
    change quotient (lift (G.edgeInclusion selected t)) =
      quotient (value (G.left selected) + (t : ℝ))
    rw [sum_quotient, at_vertex, zero_add]
    simpa using first
  have same_start : original 0 = linear 0 := by
    simp [original, linear, value]
  have equal := covering.eq_of_comp_eq original.continuous linear.continuous
    same_quotient 0 same_start
  refine ⟨value, ?_, ?_⟩
  · have last := congrFun equal 1
    simpa [original, linear, value] using last
  · intro e different
    have constant (t s : unitInterval) : quotient (lift (G.edgeInclusion e t)) =
        quotient (lift (G.edgeInclusion e s)) := by
      rw [along, along]
      simp only [ite_eq_right different]
    have same := covering.const_of_comp
      (lift.continuous.comp (G.edgeInclusion e).continuous) constant 0 1
    change lift (G.edgeInclusion e 0) = lift (G.edgeInclusion e 1) at same
    rw [G.edgeInclusion_zero, G.edgeInclusion_one] at same
    exact same

end Unfoldings.FiniteEmbeddedGraph
