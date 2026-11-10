module

public import Unfoldings.Examples.Tetrahedron.Vertices
public import Unfoldings.Polyhedron.CutDiskIff
public import Unfoldings.Topology.GraphRootExtension

/-! A specific tetrahedron cut tree produces a disk; the empty and full cut sets do not. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Examples.Tetrahedron

/-- Keep the three edges of the facet opposite vertex zero; cut its three spokes. -/
def retainBase : Set complex.Seam := {s | s.val < 3}

private def rootVertex : Fin 4 → Option (Fin 3) := ![none, some 0, some 1, some 2]

private def leaf (s : complex.CutSeam retainBase) : Fin 3 := ![0, 0, 0, 2, 1, 0] s.val

private def star := (Graph.noEdge (Set.univ : Set (Fin 3)) Empty).rootExtension Set.univ

private theorem star_acyclic : star.IsAcyclic := by
  let G := Graph.noEdge (Set.univ : Set (Fin 3)) Empty
  apply G.rootExtension_acyclic_of_roots_separated Set.univ (fun _ h => h)
  · intro e
    exact e.elim
  · rintro r _ s _ ⟨edges, walk⟩
    cases walk with
    | nil _ => rfl
    | @cons _ _ _ e _ _ _ => exact e.elim

private theorem cutLink_of_labels (retain : Set complex.Seam) (s : complex.CutSeam retain)
    {u v : complex.Vertex Set.univ}
    (first : vertexIndex u = endpointLabel (left s.val) false)
    (last : vertexIndex v = endpointLabel (left s.val) true) :
    (complex.cutSeamGraph retain).IsLink s u v :=
  Or.inl ⟨vertexIndex_injective (first.trans (vertexIndex_cutSeamVertex retain s false).symm),
    vertexIndex_injective (last.trans (vertexIndex_cutSeamVertex retain s true).symm)⟩

theorem base_cut_acyclic : (complex.cutSeamGraph retainBase).IsAcyclic := by
  let edges (s : complex.CutSeam retainBase) : Empty ⊕ (Set.univ : Set (Fin 3)) :=
    Sum.inr ⟨leaf s, Set.mem_univ _⟩
  apply star_acyclic.of_mapAlong (G := complex.cutSeamGraph retainBase) (H := star)
    (fun v => rootVertex (vertexIndex v)) edges
  · intro v _member
    cases rootVertex (vertexIndex v) <;>
      simp [star, Graph.rootExtension]
  · intro s u v link
    rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      simp only [vertexIndex_cutSeamVertex]
      obtain ⟨s, cut⟩ := s
      fin_cases s <;> simp [retainBase] at cut
      all_goals simp [edges, star, Graph.rootExtension, leaf, rootVertex,
        endpointLabel, left, corner, Triangle.next]
  · intro s t equal
    obtain ⟨s, hs⟩ := s
    obtain ⟨t, ht⟩ := t
    have validS : 3 ≤ s.val := Nat.le_of_not_gt hs
    have validT : 3 ≤ t.val := Nat.le_of_not_gt ht
    fin_cases s <;> fin_cases t <;>
      simp_all [retainBase, edges, leaf, Fin.ext_iff]

@[simp] theorem vertexIndex_symm (i : Fin 4) : vertexIndex (vertexEquiv.symm i) = i :=
  vertexEquiv.apply_symm_apply i

theorem base_cut_connected : (complex.cutSeamGraph retainBase).Connected := by
  let G := complex.cutSeamGraph retainBase
  have spoke_one : G.IsLink ⟨5, by norm_num [retainBase]⟩
      (vertexEquiv.symm 0) (vertexEquiv.symm 1) := by
    apply cutLink_of_labels
    all_goals norm_num [endpointLabel, left, corner, Triangle.next]
  have reach (i : Fin 4) : G.Reaches (vertexEquiv.symm 0) (vertexEquiv.symm i) := by
    fin_cases i
    · exact Graph.Reaches.refl spoke_one.left_mem
    · exact Graph.Reaches.of_isLink spoke_one
    · apply Graph.Reaches.of_isLink (e := ⟨4, by norm_num [retainBase]⟩)
      apply cutLink_of_labels
      all_goals norm_num [endpointLabel, left, corner, Triangle.next]
    · apply Graph.Reaches.of_isLink (e := ⟨3, by norm_num [retainBase]⟩)
      apply Graph.IsLink.symm
      apply cutLink_of_labels
      all_goals norm_num [endpointLabel, left, corner, Triangle.next]
  refine ⟨⟨vertexEquiv.symm 0, spoke_one.left_mem⟩, ?_⟩
  intro u _hu v _hv
  obtain ⟨i, rfl⟩ := vertexEquiv.symm.surjective u
  obtain ⟨j, rfl⟩ := vertexEquiv.symm.surjective v
  exact (reach i).symm.trans (reach j)

def baseCutDisk : complex.Realization retainBase ≃ₜ Metric.closedBall (0 : Plane) 1 :=
  convexBoundary.cutDiskHomeomorphOfTree retainBase base_cut_acyclic base_cut_connected

theorem no_disk_without_cuts :
    ¬ Nonempty (complex.Realization Set.univ ≃ₜ Metric.closedBall (0 : Plane) 1) := by
  intro disk
  obtain ⟨v, ⟨s, _b, _equal⟩⟩ :=
    ((convexBoundary.cutDisk_iff_cutSeamGraph_tree Set.univ).mp disk).connected.1
  exact s.property (Set.mem_univ _)

theorem no_disk_with_all_seams_cut :
    ¬ Nonempty (complex.Realization ∅ ≃ₜ Metric.closedBall (0 : Plane) 1) := by
  rintro ⟨disk⟩
  let := (convex_closedBall (0 : Plane) 1).contractibleSpace
    ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  let := disk.symm.surjective.connectedSpace disk.symm.continuous
  let x : complex.Cell 0 := ⟨(triangle 0).vertex 0, (triangle 0).vertex_mem 0⟩
  let y : complex.Cell 1 := ⟨(triangle 1).vertex 0, (triangle 1).vertex_mem 0⟩
  exact edist_ne_top_of_preconnected (complex.faceMap ∅ 0 x) (complex.faceMap ∅ 1 y)
    (complex.edist_faceMap_empty_of_ne (by decide : (0 : Fin 4) ≠ 1) x y)

end Unfoldings.Examples.Tetrahedron
