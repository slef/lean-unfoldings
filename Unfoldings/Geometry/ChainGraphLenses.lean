module

public import Unfoldings.Geometry.AcuteChainClosure
public import Unfoldings.Topology.OrderedGraphLenses
public import Mathlib.Topology.Order.ProjIcc

/-! The finite lens decomposition for strictly horizontal-monotone polygonal chains. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

open PlanarTopology

variable {n : ℕ} (P : PolygonalChain Plane n)

local notation "x" => EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0
local notation "y" => EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1

/-- Extend the graph of the chain constantly at each end. -/
theorem exists_continuous_graph_of_horizontal (nonempty : 0 < n)
    (progress : ∀ i, 0 < (P.edge i) 0) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      (∀ i, f ((P.vertex i) 0) = P.vertex i 1) ∧
      graphPoint f '' Set.Icc (P.vertex 0 0) (P.vertex (Fin.last n) 0) = Set.range P.path := by
  let a := x (P.vertex 0)
  let b := x (P.vertex (Fin.last n))
  have monotone := P.strictMono_linear_vertices x progress
  have ordered : a ≤ b := (monotone (show (0 : Fin (n + 1)) < Fin.last n from nonempty)).le
  have weak (i : Fin n) : 0 ≤ x (P.edge i) := (progress i).le
  have flat (i : Fin n) (zero : x (P.edge i) = 0) : P.edge i = 0 :=
    ((progress i).ne' zero).elim
  let chart := P.linearGraphHomeomorph x weak flat nonempty
  let f (t : ℝ) := y (chart.symm (Set.projIcc a b ordered t)).val
  have y_continuous : Continuous (fun p : Plane => p 1) := (y).continuous
  have continuous_f : Continuous f := y_continuous.comp
    (continuous_subtype_val.comp (chart.symm.continuous.comp (continuous_projIcc (h := ordered))))
  have at_t (t : Set.Icc a b) : graphPoint f t.val = (chart.symm t).val := by
    have coordinate : x (chart.symm t).val = t.val :=
      congrArg Subtype.val (chart.apply_symm_apply t)
    apply PiLp.ext
    intro j
    fin_cases j
    · exact coordinate.symm
    · change f t.val = y (chart.symm t).val
      unfold f
      rw [Set.projIcc_of_mem _ t.property]
  have at_p (p : Set.range P.path) : graphPoint f (x p.val) = p.val := by
    have equal := at_t (chart p)
    rw [chart.symm_apply_apply] at equal
    exact equal
  refine ⟨f, continuous_f, ?_, ?_⟩
  · intro i
    have equal := congrArg (fun p : Plane => p 1)
      (at_p ⟨P.vertex i, P.vertex_mem_path_range i⟩)
    exact equal
  · ext p
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [at_t ⟨t, ht⟩]
      exact (chart.symm ⟨t, ht⟩).property
    · intro member
      let q : Set.range P.path := ⟨p, member⟩
      exact ⟨x p, (chart q).property, at_p q⟩

/-- Two horizontally monotone chains with common endpoints and finitely many
contacts have an ordered family of genuine Jordan lenses. -/
theorem exists_chain_graphLenses {m : ℕ} (Q : PolygonalChain Plane m)
    (n_pos : 0 < n) (m_pos : 0 < m)
    (P_progress : ∀ i, 0 < (P.edge i) 0) (Q_progress : ∀ i, 0 < (Q.edge i) 0)
    (start : Q.vertex 0 = P.vertex 0) (finish : Q.vertex (Fin.last m) = P.vertex (Fin.last n))
    (finite : (Set.range P.path ∩ Set.range Q.path).Finite) :
    let a := P.vertex 0 0
    let b := P.vertex (Fin.last n) 0
    ∃ (f g : ℝ → ℝ) (k : ℕ) (crossing : Fin (k + 2) ↪o ℝ),
      Continuous f ∧ Continuous g ∧
      graphPoint f '' Set.Icc a b = Set.range P.path ∧
      graphPoint g '' Set.Icc a b = Set.range Q.path ∧
      crossing 0 = a ∧ crossing (Fin.last (k + 1)) = b ∧
      Set.range crossing = {t ∈ Set.Icc a b | f t = g t} ∧
      Set.range crossing = x '' (Set.range P.path ∩ Set.range Q.path) ∧
      (∀ i : Fin (k + 1), Schoenflies.IsJordanCurve
        (graphLens f g (crossing i.castSucc) (crossing i.succ))) ∧
      (Pairwise fun i j : Fin (k + 1) => Disjoint
        (interior (closedJordanDomain (graphLens f g (crossing i.castSucc) (crossing i.succ))))
        (interior (closedJordanDomain (graphLens f g (crossing j.castSucc) (crossing j.succ))))) ∧
      ∀ i : Fin (k + 1), Disjoint
        (interior (closedJordanDomain (graphLens f g (crossing i.castSucc) (crossing i.succ))))
        (Set.range P.path ∪ Set.range Q.path) := by
  let a := P.vertex 0 0
  let b := P.vertex (Fin.last n) 0
  obtain ⟨f, hf, f_vertices, range_f⟩ := P.exists_continuous_graph_of_horizontal n_pos P_progress
  obtain ⟨g, hg, g_vertices, range_g⟩ := Q.exists_continuous_graph_of_horizontal m_pos Q_progress
  have aligned_g : graphPoint g '' Set.Icc a b = Set.range Q.path := by
    have at_start : x (Q.vertex 0) = a := congrArg (x) start
    have at_finish : x (Q.vertex (Fin.last m)) = b := congrArg (x) finish
    rw [← at_start, ← at_finish]
    exact range_g
  have ordered : a < b := P.strictMono_linear_vertices x P_progress
    (show (0 : Fin (n + 1)) < Fin.last n from n_pos)
  have first : f a = g a := (f_vertices 0).trans (by simpa only [start] using (g_vertices 0).symm)
  have last : f b = g b := (f_vertices (Fin.last n)).trans
    (by simpa only [finish] using (g_vertices (Fin.last m)).symm)
  have all_contacts : {t ∈ Set.Icc a b | f t = g t} = x '' (Set.range P.path ∩ Set.range Q.path) := by
    ext t
    constructor
    · rintro ⟨ht, agrees⟩
      have equal : graphPoint f t = graphPoint g t := by simp [graphPoint, agrees]
      refine ⟨graphPoint f t, ?_, rfl⟩
      exact ⟨range_f.subset ⟨t, ht, rfl⟩, aligned_g.subset ⟨t, ht, equal.symm⟩⟩
    · rintro ⟨p, ⟨on_f, on_g⟩, rfl⟩
      obtain ⟨s, hs, rfl⟩ := range_f.symm.subset on_f
      obtain ⟨t, _, equal⟩ := aligned_g.symm.subset on_g
      have time_eq : t = s := congrArg x equal
      subst t
      exact ⟨hs, (congrArg y equal).symm⟩
  obtain ⟨k, crossing, lo, hi, all_times, simple, separated, avoid⟩ :=
    exists_ordered_graphLenses f g hf hg ordered first last (all_contacts.symm ▸ finite.image x)
  refine ⟨f, g, k, crossing, hf, hg, range_f, aligned_g, lo, hi, all_times, all_times.trans all_contacts,
    simple, separated, fun i => (avoid i).mono_right ?_⟩
  exact Set.union_subset_union (range_f.symm.subset.trans (Set.image_subset_range _ _))
    (aligned_g.symm.subset.trans (Set.image_subset_range _ _))

end Unfoldings.PolygonalChain
