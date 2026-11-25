module

public import Unfoldings.Roof.AffineFloorParentExcess
public import Unfoldings.Roof.HorizontalReorientation
public import Unfoldings.Roof.GraphBankCornerSum
public import Unfoldings.Geometry.GraphWindowSide

/-! The actual one-sided graph sum belongs to the original mesh, independently of closing refinement. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem projectedCornerAngle_reorient (E : Plane ≃ₗᵢ[ℝ] Plane) (f : Face) (i : Fin 3) :
    ((K.reorient E).projectedTriangle f).cornerAngle i = (K.projectedTriangle f).cornerAngle i := by
  have position (j : Fin 3) :
      ((K.reorient E).projectedTriangle f).vertex j = E ((K.projectedTriangle f).vertex j) :=
    K.projectFace_reorient E f ((C.triangle f).vertex j)
  simp only [Triangle.cornerAngle, EuclideanGeometry.angle, vsub_eq_sub, position, ← map_sub]
  exact E.toLinearIsometry.angle_map _ _

end Unfoldings.ConvexRoof

namespace Unfoldings.SpatialEnvelope.FloorMesh

open PlanarTopology

universe u

variable {I J : Type u} [Fintype I] [Nonempty I]
  {family : I → SpatialPlane} {floor : Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (T : FloorMesh family floor extra Z)
  (E : Plane ≃ₗᵢ[ℝ] Plane) (f : ℝ → ℝ) (a b : ℝ)

local instance oldGraphAngleIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- Original corner discrepancies along the upper bank in an open chart window.
A coarse triangle may straddle an end line. Only its portion in the window selects the side. -/
def chartBankCornerSum : ℝ := by
  classical
  exact ∑ d : T.pairedComplex.Corner,
    if E ((T.projectedTriangle d.1).vertex d.2) ∈ graphPoint f '' Set.Ioo a b ∧
      interiorAboveGraph f a b (E '' (T.projectedTriangle d.1).carrier)
    then (T.triangle d.1).cornerAngle d.2 - (T.projectedTriangle d.1).cornerAngle d.2 else 0

namespace LineRefinement

variable {T} {A : Type u} {equation : A → Plane →ᵃ[ℝ] ℝ} (L : T.LineRefinement equation)
  (inside : (interior (clipAbove family floor Z)).Nonempty)

local instance refinedGraphAnglesFintype : Fintype L.mesh.Index := @Fintype.ofFinite _ L.mesh.finite

local notation "Q" => ConvexRoof.reorient (L.mesh.roof inside) E

open Classical in
private theorem sum_grouped_graph_weights {V L' : Type*} [Fintype V]
    (groups : Finset L') (label : V → L') (all : ∀ i, label i ∈ groups)
    (keep : L' → Prop) (weight : V → ℝ) :
    (∑ i, if keep (label i) then weight i else 0) =
    ∑ j ∈ groups, if keep j then (∑ i : V, if label i = j then weight i else 0) else 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := groups) (fun i _ => all i)]
  apply Finset.sum_congr rfl
  intro j _
  by_cases selected : keep j
  · rw [ite_eq_left selected]
    calc
      _ = ∑ i ∈ Finset.univ.filter (fun i : V => label i = j), weight i :=
        Finset.sum_congr rfl (fun i hi => ite_eq_left ((Finset.mem_filter.mp hi).2 ▸ selected))
      _ = _ := Finset.sum_filter _ _
  · rw [ite_eq_right selected]
    apply Finset.sum_eq_zero
    intro i hi
    exact ite_eq_right ((Finset.mem_filter.mp hi).2 ▸ selected)

open Classical in
set_option maxHeartbeats 2100000 in
/-- The upper bank's turn sum on any aligned fine mesh is exactly the coarse
one-sided angle sum. Fine vertices in open parent edges contribute zero. -/
theorem graphBankAngleSum_eq_chartBankCornerSum
    (hf : Continuous f)
    (old_aligned : ∀ j, Disjoint (interior (E '' (T.projectedTriangle j).carrier))
      (graphPoint f '' Set.Icc a b))
    (sample : L.mesh.Index → Plane)
    (sample_in : ∀ j, sample j ∈ interior ((Q).projectedTriangle j).carrier)
    (endpoints : ∀ j z, z ∈ interior ((Q).projectedTriangle j).carrier → z 0 ≠ a ∧ z 0 ≠ b) :
    (Q).graphBankAngleSum f sample a b false = T.chartBankCornerSum E f a b := by
  let path := graphPoint f '' Set.Ioo a b
  let larger (j : T.Index) := E '' (T.projectedTriangle j).carrier
  let upper := ConvexRoof.facesAboveGraph sample f a b
  let child := L.mesh.pairedComplex
  let parent := T.pairedComplex
  let qpos (d : child.Corner) := (L.mesh.projectedTriangle d.1).vertex d.2
  let ppos (d : parent.Corner) := (T.projectedTriangle d.1).vertex d.2
  let qweight (d : child.Corner) :=
    (L.mesh.triangle d.1).cornerAngle d.2 - (L.mesh.projectedTriangle d.1).cornerAngle d.2
  let pweight (d : parent.Corner) :=
    (T.triangle d.1).cornerAngle d.2 - (T.projectedTriangle d.1).cornerAngle d.2
  let qlabel (d : child.Corner) := (L.parent d.1, qpos d)
  let plabel (d : parent.Corner) := (d.1, ppos d)
  let keep (j : T.Index × Plane) := E j.2 ∈ path ∧ interiorAboveGraph f a b (larger j.1)
  let groups := (Finset.univ.image qlabel) ∪ (Finset.univ.image plabel)
  have q_all (d : child.Corner) : qlabel d ∈ groups :=
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have p_all (d : parent.Corner) : plabel d ∈ groups :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have fine_shape (j : L.mesh.Index) :
      ((Q).projectedTriangle j).carrier = E '' (L.mesh.projectedTriangle j).carrier := by
    rw [ConvexRoof.projectedTriangle_reorient_carrier, L.mesh.roof_projectedTriangle]
  have q_sum : (Q).graphBankAngleSum f sample a b false =
      ∑ d : child.Corner, if keep (qlabel d) then qweight d else 0 := by
    rw [(Q).graphBankAngleSum_upper_eq_cornerSum]
    apply Finset.sum_congr rfl
    intro d _
    have position : ((Q).projectedTriangle d.1).vertex d.2 = E (qpos d) := by
      have h := (L.mesh.roof inside).projectFace_reorient E d.1 (child.triangle d.1 |>.vertex d.2)
      change ((Q).projectedTriangle d.1).vertex d.2 =
        E (((L.mesh.roof inside).projectedTriangle d.1).vertex d.2) at h
      rwa [L.mesh.roof_projectedTriangle] at h
    have angle :
        ((Q).projectedTriangle d.1).cornerAngle d.2 = (L.mesh.projectedTriangle d.1).cornerAngle d.2 :=
      ((L.mesh.roof inside).projectedCornerAngle_reorient E d.1 d.2).trans
        (congrArg (fun U : Triangle => U.cornerAngle d.2) (L.mesh.roof_projectedTriangle inside d.1))
    change (if ((Q).projectedTriangle d.1).vertex d.2 ∈ path ∧ d.1 ∈ upper then
        (L.mesh.triangle d.1).cornerAngle d.2 - ((Q).projectedTriangle d.1).cornerAngle d.2 else 0) =
      (if keep (qlabel d) then qweight d else 0)
    rw [position, angle]
    by_cases on_path : E (qpos d) ∈ path
    · have window : E (qpos d) 0 ∈ Set.Ioo a b := by
        obtain ⟨s, interval, equal⟩ := on_path
        rw [← equal]
        exact interval
      let U := ((Q).projectedTriangle d.1).carrier
      have nested : U ⊆ larger (L.parent d.1) := by
        unfold U larger
        rw [fine_shape]
        exact Set.image_mono (L.contained d.1)
      have member : E (qpos d) ∈ U := position ▸ ((Q).projectedTriangle d.1).vertex_mem d.2
      have convex_U : Convex ℝ U := ((Q).projectedTriangle d.1).convex_carrier
      have convex_larger : Convex ℝ (larger (L.parent d.1)) :=
        (T.projectedTriangle _).convex_carrier.linear_image E.toLinearEquiv.toLinearMap
      have genuine : (interior U).Nonempty := ((Q).projectedTriangle d.1).interior_nonempty
      obtain ⟨p, hp, time⟩ := exists_interior_mem_window_of_mem_face convex_U genuine member window
      have graph_clear : Disjoint (interior U) (graphPoint f '' Set.Icc a b) :=
        (old_aligned (L.parent d.1)).mono_left (interior_mono nested)
      have sample_side := aboveGraph_iff_of_cell hf convex_U.interior.isPreconnected
        (endpoints d.1) graph_clear (sample_in d.1) hp
      have side : d.1 ∈ upper ↔ interiorAboveGraph f a b (larger (L.parent d.1)) :=
        (sample_side.trans (and_iff_right time)).trans
          (interiorAboveGraph_iff_of_mem_window hf convex_larger (old_aligned (L.parent d.1))
            (interior_mono nested hp) time).symm
      simp only [on_path, keep, qlabel, true_and, side, qweight]
    · simp only [on_path, keep, qlabel, false_and, ite_false]
  have decided_q : (Q).graphBankAngleSum f sample a b false =
      ∑ d : child.Corner, @ite ℝ (keep (qlabel d)) (Classical.propDecidable _) (qweight d) 0 := by
    refine q_sum.trans ?_
    apply Finset.sum_congr rfl
    intro d _
    by_cases active : keep (qlabel d)
    · exact (ite_eq_left active).trans (ite_eq_left active).symm
    · exact (ite_eq_right active).trans (ite_eq_right active).symm
  have decided_p :
      (∑ d : parent.Corner, @ite ℝ (keep (plabel d)) (Classical.propDecidable _) (pweight d) 0) =
        T.chartBankCornerSum E f a b := by
    unfold chartBankCornerSum
    apply Finset.sum_congr rfl
    intro d _
    by_cases active : keep (plabel d)
    · exact (ite_eq_left active).trans (ite_eq_left active).symm
    · exact (ite_eq_right active).trans (ite_eq_right active).symm
  refine decided_q.trans ((sum_grouped_graph_weights groups qlabel q_all keep qweight).trans ?_)
  refine Eq.trans ?_ ((sum_grouped_graph_weights groups plabel p_all keep pweight).symm.trans decided_p)
  apply Finset.sum_congr rfl
  rintro ⟨j, p⟩ _
  by_cases active : keep (j, p)
  · rw [ite_eq_left active, ite_eq_left active]
    have core (i : T.Index) :
        (∑ d : parent.Corner, @ite ℝ (plabel d = (i, p)) (Classical.propDecidable _) (pweight d) 0) =
          ∑ k : Fin 3, if (T.projectedTriangle i).vertex k = p then pweight (i, k) else 0 := by
      change (∑ d : T.Index × Fin 3,
        @ite ℝ (plabel d = (i, p)) (Classical.propDecidable _) (pweight d) 0) = _
      rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
      · apply Finset.sum_congr rfl
        intro k _
        simp only [plabel, Prod.mk.injEq, ppos, true_and]
      · intro g _ different
        apply Finset.sum_eq_zero
        intro k _
        simp only [plabel, Prod.mk.injEq, different, false_and, ite_false]
      · simp
    rw [core j]
    by_cases member : p ∈ (T.projectedTriangle j).carrier
    · have border : p ∈ frontier (T.projectedTriangle j).carrier := by
        refine ⟨subset_closure member, ?_⟩
        intro forbidden
        have moved : E p ∈ interior (E '' (T.projectedTriangle j).carrier) := by
          change E p ∈ interior (E.toHomeomorph '' (T.projectedTriangle j).carrier)
          rw [← E.toHomeomorph.image_interior]
          exact Set.mem_image_of_mem E forbidden
        exact Set.disjoint_left.mp (old_aligned j) moved (Set.image_mono Set.Ioo_subset_Icc_self active.1)
      refine Eq.trans ?_ (L.sum_parentAngleExcess_at_boundary inside j border)
      apply Finset.sum_congr rfl
      intro d _
      have test : qlabel d = (j, p) ↔ L.parent d.1 = j ∧ qpos d = p := by
        simp only [qlabel, Prod.mk.injEq]
      by_cases hit : qlabel d = (j, p)
      · exact (ite_eq_left hit).trans (ite_eq_left (test.mp hit)).symm
      · exact (ite_eq_right hit).trans (ite_eq_right (mt test.mpr hit)).symm
    · have q_no (d : child.Corner) : qlabel d ≠ (j, p) := by
        intro eq
        have contained := L.contained d.1 ((L.mesh.projectedTriangle d.1).vertex_mem d.2)
        change qpos d ∈ (T.projectedTriangle (L.parent d.1)).carrier at contained
        rw [show L.parent d.1 = j from congrArg Prod.fst eq, show qpos d = p from congrArg Prod.snd eq]
          at contained
        exact member contained
      have old_no (i : Fin 3) : (T.projectedTriangle j).vertex i ≠ p :=
        fun hit => member (hit ▸ (T.projectedTriangle j).vertex_mem i)
      trans 0
      · exact Finset.sum_eq_zero (fun d _ => ite_eq_right (q_no d))
      · exact (Finset.sum_eq_zero (fun i _ => ite_eq_right (old_no i))).symm
  · rw [ite_eq_right active, ite_eq_right active]

end LineRefinement
end Unfoldings.SpatialEnvelope.FloorMesh
