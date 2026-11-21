module

public import Unfoldings.Roof.CompletionRegularCorners
public import Unfoldings.Roof.CompletionCurve
public import Unfoldings.Roof.CompletionCombinedConstraints
public import Unfoldings.Roof.MarkedClosureCompletion
public import Unfoldings.Geometry.RadialClosureEndpointRays

/-! On a fixed physical mesh, a regular radial bank has the sharp contour budget. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

open Filter Topology Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane} {I : Type u}
  {extra : I → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra)

local instance regularHalfTurnIndexFintype : Fintype E.mesh.Index :=
  @Fintype.ofFinite _ E.mesh.finite

/-- Old edge equations detect the whole old triangle skeleton, including ghost creases
inside a supporting plane. -/
def oldEdgeEquation (i : E.mesh.Index × Fin 3) : Plane →ᵃ[ℝ] ℝ :=
  segmentEquation ((E.mesh.projectedTriangle i.1).vertex i.2)
    ((E.mesh.projectedTriangle i.1).vertex (Triangle.next i.2))

theorem oldEdgeEquation_ne_zero (i : E.mesh.Index × Fin 3) :
    E.oldEdgeEquation i ≠ 0 :=
  segmentEquation_ne_zero _ _

private theorem region_has_old_face {p : Plane} (member : p ∈ region) :
    ∃ f, p ∈ (E.mesh.projectedTriangle f).carrier :=
  Set.mem_iUnion.mp (E.mesh.cover.subset (interior_subset (E.covers (Or.inr member))))

open Classical in
/-- Once the old completion contains the curve, only old-vertex avoidance and avoidance
of old edges at the closing corner are needed for the sharp aligned bank comparison. -/
theorem sharp_radial_bank_bound_of_regular_closure {n : ℕ}
    (P : PolygonalChain Plane (n + 1)) (q c : Plane)
    (radial : P.RadialFrom q 0) (genuine : ∀ i, P.edge i ≠ 0)
    (initial : 0 < dist q (P.vertex 0))
    (progress : dist q (P.vertex 0) < dist q (P.vertex (Fin.last (n + 1))))
    (height : Plane →ₗ[ℝ] ℝ) (supported : ∀ z ∈ Set.range P.path, 0 ≤ height (z - q))
    (outside : height (c - q) < 0)
    (outward : 0 < inner ℝ (P.vertex (Fin.last (n + 1)) - q)
      (c - P.vertex (Fin.last (n + 1))))
    (jordan : Schoenflies.IsJordanCurve (P.threeSegmentClosure q c))
    (contained : P.threeSegmentClosure q c ⊆ region)
    (bank_avoids : ∀ f, Disjoint (interior (E.mesh.projectedTriangle f).carrier)
      (Set.range P.path))
    (trim_avoids : ∀ (f : E.mesh.Index) (k : Fin 3),
      P.vertex 0 ≠ (E.mesh.projectedTriangle f).vertex k ∧
      P.vertex (Fin.last (n + 1)) ≠ (E.mesh.projectedTriangle f).vertex k)
    (off_edges : ∀ i, E.oldEdgeEquation i c ≠ 0)
    (links_regular : ∀ (j : Fin 3) (t : ℝ) (f : E.mesh.Index) (k : Fin 3),
      let link := radialClosingLinks q (P.vertex 0) (P.vertex (Fin.last (n + 1))) c j
      AffineMap.lineMap link.1 link.2 t ≠ (E.mesh.projectedTriangle f).vertex k)
    (positive : 0 < φ) (small : φ < π / 2) (height_bound : (3 : ℝ) / 4 ≤ cos φ)
    (tilt : K.TiltBound φ) :
    let L := E.alignToLines (K.combinedCompletionEquations (P.markedClosureEquations q c))
      (K.combinedCompletionEquations_ne_zero _ (P.markedClosureEquations_ne_zero q c))
    letI := @Fintype.ofFinite _ L.mesh.finite
    ∃ (inside : P.threeSegmentClosure q c ⊆ interior L.cap.footprint)
      (avoids : ∀ f, Disjoint (interior (L.cap.projectedTriangle f).carrier)
        (P.threeSegmentClosure q c)),
      let contains := inside.trans interior_subset
      |∑ i ∈ L.cap.jordanGeometricBankIndices jordan contains avoids (Set.range P.path)
          (radialClosingCorners q (P.vertex 0) (P.vertex (Fin.last (n + 1))) c),
        L.cap.jordanContourTurnError jordan contains avoids i| ≤
          shallowDevelopmentHeading φ - shallowDevelopmentCurvature φ := by
  let L := E.alignToLines (K.combinedCompletionEquations (P.markedClosureEquations q c))
    (K.combinedCompletionEquations_ne_zero _ (P.markedClosureEquations_ne_zero q c))
  let : Fintype L.mesh.Index := @Fintype.ofFinite _ L.mesh.finite
  let a := P.vertex 0
  let b := P.vertex (Fin.last (n + 1))
  let J := P.threeSegmentClosure q c
  have on_skeleton {z : Plane} (member : z ∈ Set.range P.path) :
      ∃ f, z ∈ (E.mesh.projectedTriangle f).carrier ∧
        z ∉ interior (E.mesh.projectedTriangle f).carrier := by
    obtain ⟨f, hf⟩ := E.region_has_old_face (contained (Or.inl member))
    exact ⟨f, hf, fun interior => Set.disjoint_left.mp (bank_avoids f) interior member⟩
  have near_forward : ∀ᶠ t : ℝ in 𝓝[>] 0, a + t • P.edge 0 ∈ Set.range P.path := by
    have small_t : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
      eventually_nhdsWithin_of_eventually_nhds
        (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))
    filter_upwards [self_mem_nhdsWithin, small_t] with t t_positive t_small
    let s : unitInterval := ⟨t, (show 0 < t from t_positive).le, t_small.le⟩
    have same : P.point 0 s = a + t • P.edge 0 := by
      rw [PolygonalChain.point, AffineMap.lineMap_apply_module', add_comm]
      rfl
    rw [← same]
    exact P.point_mem_path_range _ _
  have near_backward : ∀ᶠ t : ℝ in 𝓝[>] 0, b + t • (-P.edge (Fin.last n)) ∈
      Set.range P.path := by
    have small_t : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
      eventually_nhdsWithin_of_eventually_nhds
        (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))
    filter_upwards [self_mem_nhdsWithin, small_t] with t t_positive t_small
    have t_pos : 0 < t := t_positive
    let s : unitInterval := ⟨1 - t, by constructor <;> linarith⟩
    have same : P.point (Fin.last n) s = b + t • (-P.edge (Fin.last n)) := by
      rw [PolygonalChain.point, PolygonalChain.edge, AffineMap.lineMap_apply_module', Fin.succ_last]
      dsimp only [s, b]
      module
    rw [← same]
    exact P.point_mem_path_range _ _
  have first_corner : E.RegularClosingCorner J a := by
    apply E.regularClosingCorner_of_locally_on_old_skeleton J a (P.edge 0) (q - a)
    · rintro f ⟨k, equal⟩
      exact (trim_avoids f k).1 equal.symm
    · exact near_forward.mono (fun _ h => on_skeleton h)
    · exact (P.eventually_mem_radialClosure_iff_initial_rays q c radial genuine initial
        progress height supported outside outward).mono (fun _ h => h.mp)
  have last_corner : E.RegularClosingCorner J b := by
    apply E.regularClosingCorner_of_locally_on_old_skeleton J b (-P.edge (Fin.last n)) (c - b)
    · rintro f ⟨k, equal⟩
      exact (trim_avoids f k).2 equal.symm
    · exact near_backward.mono (fun _ h => on_skeleton h)
    · exact (P.eventually_mem_radialClosure_iff_terminal_rays q c radial genuine progress
        height supported outside).mono (fun _ h => h.mp)
  have closing_corner : E.RegularClosingCorner J c := by
    apply E.regularClosingCorner_of_off_old_edges J c
    · exact E.region_has_old_face (contained (Or.inr (Or.inl (Or.inl
        (right_mem_segment ℝ b c)))))
    · exact fun f k member => off_edges (f, k) (segmentEquation_eq_zero member)
  have corners : ∀ p, p = a ∨ p = b ∨ p = c → E.RegularClosingCorner J p := by
    rintro _ (rfl | rfl | rfl)
    · exact first_corner
    · exact last_corner
    · exact closing_corner
  let inside : J ⊆ interior L.cap.footprint := contained.trans L.region_inside
  let avoids := L.cap_avoids_supported_curve
    (K.combinedCompletionEquations_ne_zero _ (P.markedClosureEquations_ne_zero q c))
    (fun p member => by
      obtain ⟨j, equal⟩ := P.markedClosureEquations_support q c p member
      exact ⟨Sum.inr j, equal⟩)
  refine ⟨inside, avoids, ?_⟩
  exact E.alignToLines_sharp_radial_bank_bound _ _ P q c initial progress height
    (supported a (P.vertex_mem_path_range 0)) (supported b (P.vertex_mem_path_range _))
    outside outward positive.le small
    (fun i => height_bound.trans (K.completionPlanes_tilt positive small tilt _ i))
    corners links_regular (L.cap_tilt positive small tilt) jordan inside avoids

end Unfoldings.ConvexRoof.CompletionMesh
