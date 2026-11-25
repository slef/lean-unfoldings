module

public import Unfoldings.Roof.CurvatureNonnegative
public import Unfoldings.Roof.ProjectedFlatness
public import Unfoldings.Roof.Boundary
public import Unfoldings.Complex.RegionalCorners
public import Unfoldings.Geometry.JordanTriangleSelection
public import Unfoldings.Topology.SignedGraphLenses

/-! Signed lens angles can be computed by subtracting two face regions on the same roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open PlanarTopology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The incidence sum of intrinsic angle minus projected angle on an original face region. -/
def regionalAngleExcess (faces : Set Face) (v : C.Vertex Set.univ) : ℝ :=
  C.regionalCornerSum faces
    (fun c => (C.triangle c.1).cornerAngle c.2 - (K.projectedTriangle c.1).cornerAngle c.2) v

/-- The projected triangles on the filled side of an aligned Jordan boundary. -/
def graphLensFaces (J : Set Plane) : Set Face :=
  ConvexCellRegion.selected (fun j => (K.projectedTriangle j).carrier) (closedJordanDomain J)

theorem graphLensFace_subset_domain {J : Set Plane}
    (jordan : Schoenflies.IsJordanCurve J)
    (aligned : ∀ j, Disjoint (interior (K.projectedTriangle j).carrier) J)
    (j : Face) (selected : j ∈ K.graphLensFaces J) :
    (K.projectedTriangle j).carrier ⊆ closedJordanDomain J := by
  apply ConvexCellRegion.cell_subset_of_selected _ _ j isClosed_closure
    (K.projectedTriangle j).compact_carrier.isClosed (K.projectedTriangle j).convex_carrier
    (K.projectedTriangle j).interior_nonempty _ selected
  change Disjoint (interior (K.projectedTriangle j).carrier) (frontier (closedJordanDomain J))
  rw [frontier_closedJordanDomain jordan]
  exact aligned j

/-- Select the projected face samples strictly above a graph and within its horizontal interval. -/
def facesAboveGraph (sample : Face → Plane) (f : ℝ → ℝ) (a b : ℝ) : Set Face :=
  {i | sample i 0 ∈ Set.Ioo a b ∧ f (sample i 0) < sample i 1}

set_option maxHeartbeats 1200000 in
open Classical in
/-- At every vertex, the signed sum of lens fan angles is the difference
of the fan angles for the two regions above the graphs. Both regions are
evaluated on one common refinement of the roof. -/
theorem regionalAngleExcess_sub_eq_sum_graphLenses {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) {a b : ℝ} {n : ℕ}
    (c : Fin (n + 2) ↪o ℝ) (first : c 0 = a) (last : c (Fin.last (n + 1)) = b)
    (crossing : Set.range c = {t ∈ Set.Icc a b | f t = g t})
    (jordan : ∀ i : Fin (n + 1), Schoenflies.IsJordanCurve
      (graphLens f g (c i.castSucc) (c i.succ)))
    (aligned : ∀ (i : Fin (n + 1)) j, Disjoint (interior (K.projectedTriangle j).carrier)
      (graphLens f g (c i.castSucc) (c i.succ)))
    (sample : Face → Plane) (sample_in : ∀ j, sample j ∈ interior (K.projectedTriangle j).carrier)
    (sample_off : ∀ j, sample j 0 ∈ Set.Ioo a b →
      sample j 1 ≠ f (sample j 0) ∧ sample j 1 ≠ g (sample j 0))
    (w : C.Vertex Set.univ) :
    K.regionalAngleExcess (facesAboveGraph sample f a b) w -
      K.regionalAngleExcess (facesAboveGraph sample g a b) w =
        ∑ i : Fin (n + 1), graphLensSign f g (c i.castSucc) (c i.succ) *
          K.regionalAngleExcess (K.graphLensFaces (graphLens f g (c i.castSucc) (c i.succ))) w := by
  let J (i : Fin (n + 1)) := graphLens f g (c i.castSucc) (c i.succ)
  let sign (i : Fin (n + 1)) := graphLensSign f g (c i.castSucc) (c i.succ)
  have selected (i : Fin (n + 1)) (j : Face) :
      (sample j ∈ interior (closedJordanDomain (J i))) ↔ j ∈ K.graphLensFaces (J i) := by
    constructor
    · intro member
      exact TriangleFamily.jordanDomain_incident_triangle_selected K.projectedTriangle j member
        (interior_subset (sample_in j))
    · intro member
      exact interior_mono (K.graphLensFace_subset_domain (jordan i) (aligned i) j member) (sample_in j)
  have upper_weight (h : ℝ → ℝ) (j : Face) :
      (if j ∈ facesAboveGraph sample h a b then (1 : ℝ) else 0) =
        upperGraphWeight h a b (sample j) := by
    unfold upperGraphWeight
    by_cases selected : j ∈ facesAboveGraph sample h a b
    · have condition : sample j 0 ∈ Set.Ioo a b ∧ h (sample j 0) < sample j 1 := selected
      rw [ite_eq_left selected, ite_eq_left condition]
    · have condition : ¬ (sample j 0 ∈ Set.Ioo a b ∧ h (sample j 0) < sample j 1) := selected
      rw [ite_eq_right selected, ite_eq_right condition]
  have weight (j : Face) :
      ((if j ∈ facesAboveGraph sample f a b then 1 else 0) -
        (if j ∈ facesAboveGraph sample g a b then 1 else 0) : ℝ) =
          ∑ i, sign i * (if j ∈ K.graphLensFaces (J i) then 1 else 0) := by
    calc
      _ = upperGraphWeight f a b (sample j) - upperGraphWeight g a b (sample j) := by
        rw [upper_weight f j, upper_weight g j]
      _ = ∑ i, sign i * (if sample j ∈ interior (closedJordanDomain (J i)) then 1 else 0) :=
        upperGraphWeight_sub_eq_sum_lenses hf hg c first last crossing (sample j) (sample_off j)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        have iff_selected := selected i j
        by_cases member : j ∈ K.graphLensFaces (J i)
        · rw [ite_eq_left (iff_selected.mpr member), ite_eq_left member]
        · rw [ite_eq_right (fun filled => member (iff_selected.mp filled)), ite_eq_right member]
  let excess (k : C.Corner) := (C.triangle k.1).cornerAngle k.2 -
    (K.projectedTriangle k.1).cornerAngle k.2
  simp only [regionalAngleExcess, TriangleComplex.regionalCornerSum]
  rw [← Finset.sum_sub_distrib]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases incident : C.vertexOfCorner Set.univ k = w
  · have h := congrArg (fun z : ℝ => z * excess k) (weight k.1)
    simpa only [incident, and_true, sub_mul, Finset.sum_mul, ite_mul, one_mul, zero_mul, mul_assoc]
      using h
  · simp only [incident, and_false, ite_false, mul_zero, Finset.sum_const_zero, sub_self]

/-- Each triangle contributes zero total angle excess, even in a face subregion. -/
theorem sum_regionalAngleExcess (faces : Set Face) :
    (∑ v : C.Vertex Set.univ, K.regionalAngleExcess faces v) = 0 := by
  classical
  simp only [regionalAngleExcess]
  rw [C.sum_regionalCornerSum, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro f _
  by_cases member : f ∈ faces
  · simp only [member, ite_eq_left, Finset.sum_sub_distrib, Triangle.sum_cornerAngle, sub_self]
  · simp [member]

private theorem regionalAngleExcess_of_fullStar (faces : Set Face) (v : C.Vertex Set.univ)
    (full : C.FullStarIn faces v) :
    K.regionalAngleExcess faces v = C.totalAngle Set.univ v - K.projectedTotalAngle Set.univ v := by
  classical
  rw [regionalAngleExcess, C.regionalCornerSum_of_fullStar faces _ v full]
  simp only [TriangleComplex.totalAngle, projectedTotalAngle, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases same : C.vertexOfCorner Set.univ c = v <;> simp [same]

private theorem graphLens_regionalAngleExcess_eq_neg_defect {J : Set Plane}
    (jordan : Schoenflies.IsJordanCurve J) (contained : J ⊆ interior K.footprint)
    (w : C.Vertex Set.univ) (inside : K.projectedVertex w ∈ interior (closedJordanDomain J)) :
    K.regionalAngleExcess (K.graphLensFaces J) w = -C.interiorAngularDefect Set.univ w := by
  have full : C.FullStarIn (K.graphLensFaces J) w := by
    intro c same
    apply TriangleFamily.jordanDomain_incident_triangle_selected K.projectedTriangle c.1 inside
    rw [← same, K.projectedVertex_ofCorner]
    exact (K.projectedTriangle c.1).vertex_mem c.2
  have compact : IsCompact K.footprint := by
    rw [K.footprint_eq_union_projectedTriangles]
    exact isCompact_iUnion (fun f => (K.projectedTriangle f).compact_carrier)
  have enclosed := closedJordanDomain_subset_interior jordan
    (closedJordanDomain_subset_convex jordan compact K.convex_projection
      (contained.trans interior_subset)) contained
  have internal : ¬ C.IsBoundaryVertex Set.univ w :=
    (K.projectedVertex_mem_interior_iff w).mp (enclosed (interior_subset inside))
  rw [K.regionalAngleExcess_of_fullStar _ _ full, K.projectedTotalAngle_eq_two_pi w internal]
  simp only [TriangleComplex.interiorAngularDefect, ite_eq_right internal, neg_sub]

private theorem graphLens_regionalAngleExcess_eq_zero {J : Set Plane}
    (jordan : Schoenflies.IsJordanCurve J)
    (aligned : ∀ j, Disjoint (interior (K.projectedTriangle j).carrier) J)
    (w : C.Vertex Set.univ) (outside : K.projectedVertex w ∉ closedJordanDomain J) :
    K.regionalAngleExcess (K.graphLensFaces J) w = 0 := by
  classical
  unfold regionalAngleExcess TriangleComplex.regionalCornerSum
  apply Finset.sum_eq_zero
  intro c _
  apply ite_eq_right
  rintro ⟨selected, same⟩
  apply outside
  apply K.graphLensFace_subset_domain jordan aligned c.1 selected
  rw [← same, K.projectedVertex_ofCorner]
  exact (K.projectedTriangle c.1).vertex_mem c.2

set_option maxHeartbeats 1700000 in
open Classical in
/-- The actual lens comparison on a convex roof uses just the total intrinsic
curvature of that roof, with no assumption on the shape of its spatial rim. -/
theorem abs_graphLens_faceAngleDifference_add_correction_le_curvature {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) {a b : ℝ} {n : ℕ}
    (c : Fin (n + 2) ↪o ℝ) (first : c 0 = a) (last : c (Fin.last (n + 1)) = b)
    (crossing : Set.range c = {t ∈ Set.Icc a b | f t = g t})
    (sample : Face → Plane) (sample_in : ∀ j, sample j ∈ interior (K.projectedTriangle j).carrier)
    (sample_off : ∀ j, sample j 0 ∈ Set.Ioo a b →
      sample j 1 ≠ f (sample j 0) ∧ sample j 1 ≠ g (sample j 0))
    (curve : Set Plane)
    (correction : C.Vertex Set.univ → ℝ)
    (correction_bound : ∀ w, |correction w| ≤ C.interiorAngularDefect Set.univ w)
    (correction_support : ∀ w, K.projectedVertex w ∉ curve → correction w = 0) :
    let J (i : Fin (n + 1)) := graphLens f g (c i.castSucc) (c i.succ)
    (∀ i, Schoenflies.IsJordanCurve (J i)) →
    (∀ i, J i ⊆ interior K.footprint) →
    (∀ i j, Disjoint (interior (K.projectedTriangle j).carrier) (J i)) →
    (∀ i, J i ⊆ curve) →
    (∀ i, Disjoint (interior (closedJordanDomain (J i))) curve) →
    (Pairwise fun i j => Disjoint (interior (closedJordanDomain (J i)))
      (interior (closedJordanDomain (J j)))) →
    |(∑ w : C.Vertex Set.univ, if K.projectedVertex w ∈ curve then
      K.regionalAngleExcess (facesAboveGraph sample f a b) w -
        K.regionalAngleExcess (facesAboveGraph sample g a b) w else 0) +
          ∑ w, correction w| ≤ C.totalInteriorAngularDefect Set.univ := by
  dsimp only
  let J (i : Fin (n + 1)) := graphLens f g (c i.castSucc) (c i.succ)
  let sign (i : Fin (n + 1)) := graphLensSign f g (c i.castSucc) (c i.succ)
  intro jordan inside aligned boundary avoids disjoint
  let δ (w : C.Vertex Set.univ) := C.interiorAngularDefect Set.univ w
  let domain (i : Fin (n + 1)) := interior (closedJordanDomain (J i))
  let d (w : C.Vertex Set.univ) :=
    K.regionalAngleExcess (facesAboveGraph sample f a b) w -
      K.regionalAngleExcess (facesAboveGraph sample g a b) w
  let q (i : Fin (n + 1)) (w : C.Vertex Set.univ) :=
    if K.projectedVertex w ∈ domain i then sign i * δ w else 0
  let qTotal (w : C.Vertex Set.univ) := ∑ i, q i w
  let boundarySum (w : C.Vertex Set.univ) := if K.projectedVertex w ∈ curve then d w else 0
  have balance (w : C.Vertex Set.univ) : d w = boundarySum w - qTotal w := by
    by_cases w_curve : K.projectedVertex w ∈ curve
    · have q_zero (i : Fin (n + 1)) : q i w = 0 :=
        ite_eq_right (fun fill => Set.disjoint_left.mp (avoids i) fill w_curve)
      simp only [boundarySum, w_curve, ite_true, qTotal, q_zero, Finset.sum_const_zero, sub_zero]
    · rw [show boundarySum w = 0 from ite_eq_right w_curve, zero_sub]
      unfold d qTotal
      rw [K.regionalAngleExcess_sub_eq_sum_graphLenses hf hg c first last crossing jordan aligned
        sample sample_in sample_off w, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases enclosed : K.projectedVertex w ∈ domain i
      · rw [show q i w = sign i * δ w from ite_eq_left enclosed,
          K.graphLens_regionalAngleExcess_eq_neg_defect (jordan i) (inside i) w enclosed, mul_neg]
      · have outside : K.projectedVertex w ∉ closedJordanDomain (J i) := by
          intro filled
          have on_border : K.projectedVertex w ∈ frontier (closedJordanDomain (J i)) :=
            ⟨subset_closure filled, enclosed⟩
          exact w_curve (boundary i ((frontier_closedJordanDomain (jordan i)).subset on_border))
        rw [show q i w = 0 from ite_eq_right enclosed,
          K.graphLens_regionalAngleExcess_eq_zero (jordan i) (aligned i) w outside, mul_zero, neg_zero]
  have all : (∑ w, d w) = 0 := by
    simp only [d, Finset.sum_sub_distrib, K.sum_regionalAngleExcess, sub_self]
  have sums := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun w _ => balance w)
  rw [all, Finset.sum_sub_distrib] at sums
  have boundary_total : (∑ w, boundarySum w) = ∑ w, qTotal w := sub_eq_zero.mp sums.symm
  have pointwise (w : C.Vertex Set.univ) : |qTotal w + correction w| ≤ δ w := by
    by_cases enclosed : ∃ i, K.projectedVertex w ∈ domain i
    · obtain ⟨i, filled⟩ := enclosed
      have single : qTotal w = sign i * δ w := by
        calc
          _ = q i w := by
            apply Finset.sum_eq_single i
            · intro j _ different
              exact ite_eq_right (fun hit => Set.disjoint_left.mp (disjoint different) hit filled)
            · simp
          _ = _ := ite_eq_left filled
      have not_curve : K.projectedVertex w ∉ curve :=
        fun hc => Set.disjoint_left.mp (avoids i) filled hc
      have signed : |sign i| = 1 := by
        simp only [sign, graphLensSign]
        split_ifs <;> norm_num
      rw [single, correction_support w not_curve, add_zero, abs_mul, signed,
        one_mul, abs_of_nonneg (K.interiorCurvature_nonneg w)]
    · have no_lens (i : Fin (n + 1)) : q i w = 0 :=
        ite_eq_right (fun member => enclosed ⟨i, member⟩)
      simp only [qTotal, no_lens, Finset.sum_const_zero, zero_add, δ, correction_bound]
  change |(∑ w, boundarySum w) + ∑ w, correction w| ≤ _
  rw [boundary_total, ← Finset.sum_add_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun w _ => pointwise w))

end Unfoldings.ConvexRoof
