module

public import Schoenflies.Graph.Cycle
public import Mathlib.Data.List.OfFn

/-! Distinct finite vertex sequences construct actual paths in multigraphs. -/

@[expose] public section

namespace Graph

variable {V E : Type*} (G : Graph V E)

theorem isPath_of_fin_sequence {n : ℕ} (vertices : Fin (n + 1) → V) (edges : Fin n → E)
    (members : ∀ i, vertices i ∈ G.vertexSet)
    (links : ∀ i, G.IsLink (edges i) (vertices i.castSucc) (vertices i.succ))
    (injective : Function.Injective vertices) :
    G.IsPath (vertices 0) (List.ofFn edges) (vertices (Fin.last n)) := by
  induction n with
  | zero =>
    simpa using IsPath.nil (members 0)
  | succ n ih =>
    rw [List.ofFn_succ]
    refine IsPath.cons (links 0) ?_ ?_
    · apply ih (fun i => vertices i.succ) (fun i => edges i.succ)
        (fun i => members i.succ) (fun i => ?_)
        (fun i j same => Fin.succ_injective _ (injective same))
      simpa only [Fin.succ_castSucc] using links i.succ
    · intro visited
      rcases mem_walkVertices_iff.mp visited with same | covered
      · have indices := congrArg Fin.val (injective same)
        simp at indices
      · obtain ⟨edge, member, incidence⟩ := covered
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
        rcases incidence.eq_or_eq_of_isLink (links i.succ) with same | same
        · have indices := congrArg Fin.val (injective same)
          simp at indices
        · have indices := congrArg Fin.val (injective same)
          simp at indices

theorem isCycleThrough_of_fin_sequence {n : ℕ}
    (vertices : Fin (n + 1) → V) (edges : Fin (n + 1) → E)
    (members : ∀ i, vertices i ∈ G.vertexSet)
    (links : ∀ i : Fin n,
      G.IsLink (edges i.castSucc) (vertices i.castSucc) (vertices i.succ))
    (closes : G.IsLink (edges (Fin.last n)) (vertices (Fin.last n)) (vertices 0))
    (vertices_injective : Function.Injective vertices)
    (edges_injective : Function.Injective edges) :
    G.IsCycleThrough (edges (Fin.last n)) (vertices 0) (vertices (Fin.last n))
      (List.ofFn (fun i : Fin n => edges i.castSucc)) := by
  refine ⟨closes.symm, G.isPath_of_fin_sequence vertices _ members links vertices_injective, ?_⟩
  intro member
  obtain ⟨i, same⟩ := List.mem_ofFn.mp member
  have indices := congrArg Fin.val (edges_injective same)
  simp only [Fin.val_castSucc, Fin.val_last] at indices
  omega

end Graph
