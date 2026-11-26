module

public import Unfoldings.Roof.GraphBankSharpBudget
public import Unfoldings.Roof.SupportedNormalTrace

/-! The signed graph balance uses a single normal ribbon for the whole bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open PlanarTopology Cap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
set_option maxHeartbeats 1900000 in
/-- Balance a bank against a horizontal long link and a flat short tail.
The long link's normal transport cancels the radial part of the two end errors. -/
theorem abs_graphBankAngleSum_le_signed {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (order : a < b) (start : f a = g a) (finish : f b = g b)
    (finite : {t ∈ Set.Icc a b | f t = g t}.Finite)
    (sample : Face → Plane) (sample_in : ∀ j, sample j ∈ interior (K.projectedTriangle j).carrier)
    (endpoints : ∀ i z, z ∈ interior (K.projectedTriangle i).carrier → z 0 ≠ a ∧ z 0 ≠ b)
    (aligned_f : ∀ j, Disjoint (interior (K.projectedTriangle j).carrier) (graphPoint f '' Set.Icc a b))
    (aligned_g : ∀ j, Disjoint (interior (K.projectedTriangle j).carrier) (graphPoint g '' Set.Icc a b))
    (contained : (graphPoint f '' Set.Icc a b) ∪ (graphPoint g '' Set.Icc a b) ⊆ interior K.footprint)
    (flat_g : ∀ w : C.Vertex Set.univ, K.projectedVertex w ∈ graphPoint g '' Set.Ioo a b →
      C.interiorAngularDefect Set.univ w = 0)
    (left right : C.Vertex Set.univ)
    (at_left : K.projectedVertex left = graphPoint f a) (at_right : K.projectedVertex right = graphPoint f b)
    {cutoff level : ℝ} (horizontal : ∀ x ∈ Set.Ioo a b, x ≤ cutoff → g x = level)
    (flat_tail : ∀ w : C.Vertex Set.univ, cutoff < K.projectedVertex w 0 →
      K.projectedVertex w 0 ∈ Set.Ioo a b →
      K.projectedVertex w 1 ∈ Set.uIcc (f (K.projectedVertex w 0)) (g (K.projectedVertex w 0)) →
      C.interiorAngularDefect Set.univ w = 0)
    {cell : Set Plane} (compact : IsCompact cell) (convex : Convex ℝ cell)
    (slopes : ∀ f, K.normalSlope f ∈ cell)
    {m : ℕ} (T : K.SupportedNormalTrace cell level (m + 1)) {closingError endpointError : ℝ}
    (closing : |(∑ w : C.Vertex Set.univ, if K.projectedVertex w ∈ graphPoint g '' Set.Ioo a b then
      K.regionalAngleExcess (facesAboveGraph sample g a b) w else 0) + T.hingeSum| ≤ closingError)
    (end_charge : let F := K.regionalAngleExcess (facesAboveGraph sample f a b)
      let G := K.regionalAngleExcess (facesAboveGraph sample g a b)
      let p := T.path.vertex 0
      let q := T.path.vertex (Fin.last (m + 1))
      |(F left - G left) + (F right - G right) +
        (radialSectionHeading (q 0) (q 1) - radialSectionHeading (p 0) (p 1))| ≤ endpointError)
    (right_bank : Bool) :
    let p := T.path.vertex 0
    let q := T.path.vertex (Fin.last (m + 1))
    |K.graphBankAngleSum f sample a b right_bank| ≤
      (solidAngleMeasure (gnomonicNormal '' cell)).toReal + |p 0 * q 1 - q 0 * p 1| / 2 +
        (closingError + endpointError) := by
  obtain ⟨n, c, first, last, crossing, jordan, disjoint, avoids⟩ :=
    exists_ordered_graphLenses f g hf hg order start finish finite
  let A := K.graphBankAngleSum f sample a b right_bank
  let V := K.projectedVertex
  let δ := C.interiorAngularDefect Set.univ
  let F := K.regionalAngleExcess (facesAboveGraph sample f a b)
  let G := K.regionalAngleExcess (facesAboveGraph sample g a b)
  let B := ∑ w : C.Vertex Set.univ, if V w ∈ graphPoint g '' Set.Ioo a b then G w else 0
  let D := (F left - G left) + (F right - G right)
  let p := T.path.vertex 0
  let q := T.path.vertex (Fin.last (m + 1))
  let radial := radialSectionHeading (q 0) (q 1) - radialSectionHeading (p 0) (p 1)
  have included (i : Fin (n + 1)) : graphLens f g (c i.castSucc) (c i.succ) ⊆
      (graphPoint f '' Set.Icc a b) ∪ (graphPoint g '' Set.Icc a b) := by
    have bounded : Set.Icc (c i.castSucc) (c i.succ) ⊆ Set.Icc a b := by
      rw [← first, ← last]
      exact Set.Icc_subset_Icc (c.monotone (Fin.zero_le _)) (c.monotone (Fin.le_last _))
    exact Set.union_subset_union (Set.image_mono bounded) (Set.image_mono bounded)
  obtain ⟨w, bounded, active, balance⟩ := K.exists_signed_graph_boundaryAngleBalance hf hg c
    first last crossing sample sample_in endpoints aligned_f aligned_g flat_g right_bank
    contained jordan included (fun i => (avoids i).mono_right
      (Set.union_subset_union (Set.image_subset_range _ _) (Set.image_subset_range _ _))) disjoint
  let weight (j : C.Vertex Set.univ) := if V j 0 ≤ cutoff then w j else 0
  have w_bound (j : C.Vertex Set.univ) : |weight j| ≤ 1 := by
    unfold weight
    split
    · exact bounded j
    · simp
  have w_pos (j : C.Vertex Set.univ) (h : weight j ≠ 0) : 0 < (V j 1 - level) * weight j := by
    by_cases early : V j 0 ≤ cutoff
    · have hn : w j ≠ 0 := by simpa only [weight, if_pos early] using h
      obtain ⟨mid, _, sign⟩ := active j hn
      simpa only [weight, if_pos early, horizontal _ mid early] using sign
    · exact (h (by simp [weight, early])).elim
  have sum_eq : (∑ j, weight j * δ j) = ∑ j, w j * δ j := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hz : w j = 0
    · simp [weight, hz]
    by_cases h : V j 0 ≤ cutoff
    · simp [weight, h]
    · obtain ⟨mid, between, _⟩ := active j hz
      have zero : δ j = 0 := flat_tail j (lt_of_not_ge h) mid between
      simp only [zero, mul_zero]
  have transport := T.abs_signed_defects_add_hingeSum_sub_radial_le (Nat.succ_pos m)
    compact convex slopes weight w_bound
    (fun j => by
      by_cases zero : weight j = 0
      · simp [zero]
      · exact (w_pos j zero).le)
    (fun j on => by
      by_contra h
      have pos := w_pos j h
      rw [on, sub_self, zero_mul] at pos
      exact (lt_irrefl 0) pos)
  change |(∑ j, weight j * δ j) + T.hingeSum - radial| ≤ _ at transport
  rw [sum_eq, ← balance, K.graph_endpoint_sum_eq sample order start finish left right at_left at_right]
    at transport
  change |-(A - B + D) + T.hingeSum - radial| ≤ _ at transport
  change |B + T.hingeSum| ≤ closingError at closing
  change |D + radial| ≤ endpointError at end_charge
  have eq : -A = (-(A - B + D) + T.hingeSum - radial) + (-(B + T.hingeSum) + (D + radial)) := by ring
  change |A| ≤ _
  rw [← abs_neg A, eq]
  refine (abs_add_le _ _).trans (add_le_add transport ?_)
  exact (abs_add_le _ _).trans (add_le_add (by simpa only [abs_neg] using closing) end_charge)

end Unfoldings.ConvexRoof
