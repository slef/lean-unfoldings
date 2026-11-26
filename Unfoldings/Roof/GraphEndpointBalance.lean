module

public import Unfoldings.Roof.GraphLensCornerFan

/-! The two end lines contribute just the two sharp endpoint angle errors. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open PlanarTopology Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) {a b : ℝ} {n : ℕ}
  (c : Fin (n + 2) ↪o ℝ) (first : c 0 = a) (last : c (Fin.last (n + 1)) = b)
  (crossing : Set.range c = {t ∈ Set.Icc a b | f t = g t})
  (jordan : ∀ i : Fin (n + 1), Schoenflies.IsJordanCurve (graphLens f g (c i.castSucc) (c i.succ)))
  (aligned : ∀ (i : Fin (n + 1)) j, Disjoint (interior (K.projectedTriangle j).carrier)
    (graphLens f g (c i.castSucc) (c i.succ)))
  (sample : Face → Plane) (sample_in : ∀ j, sample j ∈ interior (K.projectedTriangle j).carrier)
  (sample_off : ∀ j, sample j 0 ∈ Set.Ioo a b →
    sample j 1 ≠ f (sample j 0) ∧ sample j 1 ≠ g (sample j 0))

local notation "J[" i "]" => graphLens f g (c (Fin.castSucc i)) (c (Fin.succ i))
local notation "upperF" => facesAboveGraph sample f a b
local notation "upperG" => facesAboveGraph sample g a b

include hf hg first last crossing jordan aligned sample_in sample_off in
open Classical in
set_option maxHeartbeats 900000 in
/-- If only one lens can reach a vertex's vertical line, its regional error
is the difference of the two graph-side errors there, with the lens sign. -/
theorem graph_regionDifference_eq_uniqueLens (w : C.Vertex Set.univ)
    (i : Fin (n + 1))
    (outside : ∀ j : Fin (n + 1), j ≠ i → K.projectedVertex w 0 ∉ Set.Icc (c j.castSucc) (c j.succ)) :
    K.regionalAngleExcess upperF w - K.regionalAngleExcess upperG w =
      graphLensSign f g (c i.castSucc) (c i.succ) *
        K.regionalAngleExcess (K.graphLensFaces (J[i])) w := by
  have zero (j : Fin (n + 1)) (other : j ≠ i) :
      K.regionalAngleExcess (K.graphLensFaces (J[j])) w = 0 := by
    unfold regionalAngleExcess TriangleComplex.regionalCornerSum
    apply Finset.sum_eq_zero
    intro p _
    apply ite_eq_right
    rintro ⟨selected, contact⟩
    apply outside j other
    have domain : K.projectedVertex w ∈ closedJordanDomain (J[j]) := by
      apply K.graphLensFace_subset_domain (jordan j) (aligned j) p.1 selected
      rw [← contact, K.projectedVertex_ofCorner]
      exact (K.projectedTriangle p.1).vertex_mem p.2
    exact closedJordanDomain_two_graphs_subset_slab (jordan j) domain
  rw [K.regionalAngleExcess_sub_eq_sum_graphLenses hf hg c first last crossing jordan aligned
    sample sample_in sample_off w, Finset.sum_eq_single i]
  · intro j _ other
    rw [zero j other, mul_zero]
  · simp

include hf hg first last crossing jordan aligned sample_in sample_off in
/-- The initial endpoint of the two graph traces belongs only to the first lens. -/
theorem graph_regionDifference_eq_firstLens (w : C.Vertex Set.univ)
    (at_first : K.projectedVertex w 0 = a) :
    K.regionalAngleExcess upperF w - K.regionalAngleExcess upperG w =
      graphLensSign f g (c (0 : Fin (n + 1)).castSucc) (c (0 : Fin (n + 1)).succ) *
          K.regionalAngleExcess (K.graphLensFaces (J[(0 : Fin (n + 1))])) w := by
  apply K.graph_regionDifference_eq_uniqueLens hf hg c first last crossing jordan aligned
    sample sample_in sample_off w 0
  intro j different member
  have advance : 0 < (j.castSucc : Fin (n + 2)) := by
    change 0 < j.val
    exact Nat.pos_of_ne_zero (fun h => different (Fin.ext h))
  have before := c.strictMono advance
  rw [first] at before
  exact before.not_ge (at_first ▸ member.1)

include hf hg first last crossing jordan aligned sample_in sample_off in
/-- The terminal endpoint of the two graph traces belongs only to the last lens. -/
theorem graph_regionDifference_eq_lastLens (w : C.Vertex Set.univ)
    (at_last : K.projectedVertex w 0 = b) :
    K.regionalAngleExcess upperF w - K.regionalAngleExcess upperG w =
      graphLensSign f g (c (Fin.last n).castSucc) (c (Fin.last n).succ) *
        K.regionalAngleExcess (K.graphLensFaces (J[Fin.last n])) w := by
  apply K.graph_regionDifference_eq_uniqueLens hf hg c first last crossing jordan aligned
    sample sample_in sample_off w (Fin.last n)
  intro j different member
  have advance : j.succ < Fin.last (n + 1) := by
    have he : j.val ≠ n := fun h => different (Fin.ext h)
    change j.val + 1 < n + 1
    omega
  have after := c.strictMono advance
  rw [last] at after
  exact after.not_ge (at_last ▸ member.2)

include hf hg first last crossing jordan aligned sample_in sample_off in
open Classical in
set_option maxHeartbeats 900000 in
/-- If only one lens can reach a vertex's vertical line, its regional error
is the absolute difference of the two graph-side errors there. -/
theorem abs_graph_regionDifference_eq_uniqueLens (w : C.Vertex Set.univ)
    (i : Fin (n + 1))
    (outside : ∀ j : Fin (n + 1), j ≠ i → K.projectedVertex w 0 ∉ Set.Icc (c j.castSucc) (c j.succ)) :
    |K.regionalAngleExcess upperF w - K.regionalAngleExcess upperG w| =
      |K.regionalAngleExcess (K.graphLensFaces (J[i])) w| := by
  rw [K.graph_regionDifference_eq_uniqueLens hf hg c first last crossing jordan aligned
    sample sample_in sample_off w i outside, abs_mul, show
      |graphLensSign f g (c i.castSucc) (c i.succ)| = 1 by
        unfold graphLensSign
        split <;> norm_num, one_mul]

include hf hg first last crossing jordan aligned sample_in sample_off in
/-- The initial endpoint of the two graph traces belongs only to the first lens. -/
theorem abs_graph_regionDifference_eq_firstLens (w : C.Vertex Set.univ)
    (at_first : K.projectedVertex w 0 = a) :
    |K.regionalAngleExcess upperF w - K.regionalAngleExcess upperG w| =
      |K.regionalAngleExcess (K.graphLensFaces (J[(0 : Fin (n + 1))])) w| := by
  apply K.abs_graph_regionDifference_eq_uniqueLens hf hg c first last crossing jordan aligned
    sample sample_in sample_off w 0
  intro j different member
  have advance : 0 < (j.castSucc : Fin (n + 2)) := by
    change 0 < j.val
    exact Nat.pos_of_ne_zero (fun h => different (Fin.ext h))
  have before := c.strictMono advance
  rw [first] at before
  exact before.not_ge (at_first ▸ member.1)

include hf hg first last crossing jordan aligned sample_in sample_off in
/-- The terminal endpoint of the two graph traces belongs only to the last lens. -/
theorem abs_graph_regionDifference_eq_lastLens (w : C.Vertex Set.univ)
    (at_last : K.projectedVertex w 0 = b) :
    |K.regionalAngleExcess upperF w - K.regionalAngleExcess upperG w| =
      |K.regionalAngleExcess (K.graphLensFaces (J[Fin.last n])) w| := by
  apply K.abs_graph_regionDifference_eq_uniqueLens hf hg c first last crossing jordan aligned
    sample sample_in sample_off w (Fin.last n)
  intro j different member
  have advance : j.succ < Fin.last (n + 1) := by
    have he : j.val ≠ n := fun h => different (Fin.ext h)
    change j.val + 1 < n + 1
    omega
  have after := c.strictMono advance
  rw [last] at after
  exact after.not_ge (at_last ▸ member.2)


open Classical in
set_option maxHeartbeats 950000 in
/-- At a two-graph end line the only possible charge is the one physical
endpoint. The sum is the signed contribution from those two endpoints. -/
theorem graph_endpoint_sum_eq
    (order : a < b) (start : f a = g a) (finish : f b = g b)
    (left right : C.Vertex Set.univ)
    (at_left : K.projectedVertex left = graphPoint f a)
    (at_right : K.projectedVertex right = graphPoint f b) :
    let curve := (graphPoint f '' Set.Icc a b) ∪ (graphPoint g '' Set.Icc a b)
    (∑ w : C.Vertex Set.univ, if K.projectedVertex w ∈ curve ∧
      K.projectedVertex w 0 ∉ Set.Ioo a b then
        K.regionalAngleExcess upperF w - K.regionalAngleExcess upperG w else 0) =
      (K.regionalAngleExcess upperF left - K.regionalAngleExcess upperG left) +
        (K.regionalAngleExcess upperF right - K.regionalAngleExcess upperG right) := by
  let curve := (graphPoint f '' Set.Icc a b) ∪ (graphPoint g '' Set.Icc a b)
  let error (w : C.Vertex Set.univ) := K.regionalAngleExcess upperF w - K.regionalAngleExcess upperG w
  let active (w : C.Vertex Set.univ) := K.projectedVertex w ∈ curve ∧
    K.projectedVertex w 0 ∉ Set.Ioo a b
  let term (w : C.Vertex Set.univ) := if active w then error w else 0
  have active_left : active left := by
    rw [show active left ↔ K.projectedVertex left ∈ curve ∧
      K.projectedVertex left 0 ∉ Set.Ioo a b from Iff.rfl, at_left]
    exact ⟨Or.inl ⟨a, ⟨le_rfl, order.le⟩, rfl⟩, fun h => lt_irrefl a h.1⟩
  have active_right : active right := by
    rw [show active right ↔ K.projectedVertex right ∈ curve ∧
      K.projectedVertex right 0 ∉ Set.Ioo a b from Iff.rfl, at_right]
    exact ⟨Or.inl ⟨b, ⟨order.le, le_rfl⟩, rfl⟩, fun h => lt_irrefl b h.2⟩
  have where_possible (w : C.Vertex Set.univ) (hit : active w) : w = left ∨ w = right := by
    obtain ⟨on_curve, border⟩ := hit
    have point (s : ℝ) (interval : s ∈ Set.Icc a b) (end_line : s ∉ Set.Ioo a b) :
        s = a ∨ s = b := by
      by_contra! distinct
      exact end_line ⟨lt_of_le_of_ne interval.1 distinct.1.symm, lt_of_le_of_ne interval.2 distinct.2⟩
    have graphs_equal {s : ℝ} (eq : f s = g s) : graphPoint f s = graphPoint g s := by
      simp only [graphPoint, eq]
    rcases on_curve with ⟨s, interval, position⟩ | ⟨s, interval, position⟩
    · have end_line : s ∉ Set.Ioo a b := by rwa [← position] at border
      rcases point s interval end_line with rfl | rfl
      · exact Or.inl (K.projectedVertex_injective (position.symm.trans at_left.symm))
      · exact Or.inr (K.projectedVertex_injective (position.symm.trans at_right.symm))
    · have end_line : s ∉ Set.Ioo a b := by rwa [← position] at border
      rcases point s interval end_line with rfl | rfl
      · exact Or.inl (K.projectedVertex_injective
          (position.symm.trans ((graphs_equal start).symm.trans at_left.symm)))
      · exact Or.inr (K.projectedVertex_injective
          (position.symm.trans ((graphs_equal finish).symm.trans at_right.symm)))
  have distinct : left ≠ right := by
    intro eq
    have conflict : graphPoint f a = graphPoint f b :=
      at_left.symm.trans ((congrArg K.projectedVertex eq).trans at_right)
    exact order.ne (congrArg (fun z : Plane => z 0) conflict)
  have sum : (∑ w, term w) = term left + term right := by
    rw [← Finset.sum_pair distinct]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro w _ other
    apply ite_eq_right
    intro hit
    exact other (Finset.mem_insert.mpr ((where_possible w hit).imp id Finset.mem_singleton.mpr))
  change (∑ w, term w) = error left + error right
  rw [sum, show term left = error left from ite_eq_left active_left,
    show term right = error right from ite_eq_left active_right]

open Classical in
set_option maxHeartbeats 950000 in
/-- At a two-graph end line the only possible charge is the one physical
endpoint. The sum over both end lines therefore uses exactly two bounds. -/
theorem abs_graph_endpoint_sum_le
    (order : a < b) (start : f a = g a) (finish : f b = g b)
    (left right : C.Vertex Set.univ)
    (at_left : K.projectedVertex left = graphPoint f a)
    (at_right : K.projectedVertex right = graphPoint f b)
    {δ : ℝ} (left_bound : |K.regionalAngleExcess upperF left - K.regionalAngleExcess upperG left| ≤ δ)
    (right_bound : |K.regionalAngleExcess upperF right - K.regionalAngleExcess upperG right| ≤ δ) :
    let curve := (graphPoint f '' Set.Icc a b) ∪ (graphPoint g '' Set.Icc a b)
    |∑ w : C.Vertex Set.univ, if K.projectedVertex w ∈ curve ∧
      K.projectedVertex w 0 ∉ Set.Ioo a b then
        K.regionalAngleExcess upperF w - K.regionalAngleExcess upperG w else 0| ≤ 2 * δ := by
  dsimp only
  rw [K.graph_endpoint_sum_eq sample order start finish left right at_left at_right]
  exact (abs_add_le _ _).trans (by linarith only [left_bound, right_bound])

end Unfoldings.ConvexRoof
