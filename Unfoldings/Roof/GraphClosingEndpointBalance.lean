module

public import Unfoldings.Roof.GraphEndpointBalance
public import Unfoldings.Roof.SignedLensEndpoint

/-! The endpoint charge between two actual graphs is a signed heading difference. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Filter Topology PlanarTopology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
set_option maxHeartbeats 1800000 in
/-- Evaluate the first or last lens of the actual bank and closing graphs. -/
theorem graphEndpoint_excess_sub_eq_headingError {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) {a b : ℝ} (order : a < b)
    (start : f a = g a) (finish : f b = g b) (finite : {x ∈ Set.Icc a b | f x = g x}.Finite)
    (sample : Face → Plane) (sample_in : ∀ j, sample j ∈ interior (K.projectedTriangle j).carrier)
    (aligned_f : ∀ j, Disjoint (interior (K.projectedTriangle j).carrier) (graphPoint f '' Set.Icc a b))
    (aligned_g : ∀ j, Disjoint (interior (K.projectedTriangle j).carrier) (graphPoint g '' Set.Icc a b))
    (inside : (graphPoint f '' Set.Icc a b) ∪ (graphPoint g '' Set.Icc a b) ⊆ interior K.footprint)
    (initial : Bool) (w : C.Vertex Set.univ)
    (at_w : K.projectedVertex w = graphPoint f (if initial then a else b))
    {u v s t : Plane} (forward_u : 0 < (if initial then u 0 else -u 0))
    (forward_v : 0 < (if initial then v 0 else -v 0))
    (on_bank : segment ℝ (K.projectedVertex w) (K.projectedVertex w + u) ⊆ graphPoint f '' Set.Icc a b)
    (on_close : segment ℝ (K.projectedVertex w) (K.projectedVertex w + v) ⊆ graphPoint g '' Set.Icc a b)
    (slopes : ∀ i j, C.vertexOfCorner Set.univ (i, j) = w → K.normalSlope i = s ∨ K.normalSlope i = t)
    (tangent : inner ℝ (s - t) u = 0)
    (local_rays : ∀ᶠ x in 𝓝 (K.projectedVertex w),
      x ∈ (graphPoint f '' Set.Icc a b) ∪ (graphPoint g '' Set.Icc a b) →
      x - K.projectedVertex w ∈ nonnegativeRay u ∪ nonnegativeRay v)
    (ref : Face)
    (active : ∀ (i : Face) (r : ℝ), 0 < r → orient 0 u v ≠ 0 →
      (∃ k, C.vertexOfCorner Set.univ (i, k) = w) →
      K.projectedVertex w ∈ (K.projectedTriangle i).carrier →
      K.projectedVertex w + r • v ∈ (K.projectedTriangle i).carrier →
      K.normalSlope i = K.normalSlope ref) :
    K.regionalAngleExcess (facesAboveGraph sample f a b) w -
      K.regionalAngleExcess (facesAboveGraph sample g a b) w =
        (if initial then 1 else -1) * (K.sectionHeadingError ref v - K.sectionHeadingError ref u) := by
  obtain ⟨n, c, first, last, crossing, jordan, _, _⟩ :=
    exists_ordered_graphLenses f g hf hg order start finish finite
  let J (i : Fin (n + 1)) := graphLens f g (c i.castSucc) (c i.succ)
  let curve := (graphPoint f '' Set.Icc a b) ∪ (graphPoint g '' Set.Icc a b)
  have incl (i : Fin (n + 1)) :
      Set.Icc (c i.castSucc) (c i.succ) ⊆ Set.Icc a b := by
    rw [← first, ← last]
    exact Set.Icc_subset_Icc (c.monotone (Fin.zero_le _)) (c.monotone (Fin.le_last _))
  have included (i : Fin (n + 1)) : J i ⊆ curve :=
    Set.union_subset_union (Set.image_mono (incl i)) (Set.image_mono (incl i))
  have aligned (i : Fin (n + 1)) j : Disjoint (interior (K.projectedTriangle j).carrier) (J i) :=
    ((aligned_f j).union_right (aligned_g j)).mono_right (included i)
  have sample_off (j : Face) (window : sample j 0 ∈ Set.Ioo a b) :
      sample j 1 ≠ f (sample j 0) ∧ sample j 1 ≠ g (sample j 0) := by
    have on (h : ℝ → ℝ) (eq : sample j 1 = h (sample j 0)) :
        sample j ∈ graphPoint h '' Set.Icc a b := by
      refine ⟨sample j 0, Set.Ioo_subset_Icc_self window, ?_⟩
      apply PiLp.ext
      intro i
      fin_cases i
      · rfl
      · exact eq.symm
    exact ⟨fun h => Set.disjoint_left.mp (aligned_f j) (sample_in j) (on f h),
      fun h => Set.disjoint_left.mp (aligned_g j) (sample_in j) (on g h)⟩
  let i : Fin (n + 1) := if initial then 0 else Fin.last n
  have cx : K.projectedVertex w 0 = if initial then c i.castSucc else c i.succ := by
    have value := congrArg (fun z : Plane => z 0) at_w
    cases initial
    · change K.projectedVertex w 0 = b at value
      simpa only [i, Bool.false_eq_true, ite_false, Fin.succ_last, last] using value
    · change K.projectedVertex w 0 = a at value
      simpa only [i, ite_true, Fin.castSucc_zero, first] using value
  have w_in : K.projectedVertex w ∈ J i := by
    have eq : graphPoint f (K.projectedVertex w 0) = K.projectedVertex w := by rw [at_w]; rfl
    have lt := c.strictMono (Fin.castSucc_lt_succ (i := i))
    refine Or.inl ⟨_, ?_, eq⟩
    cases initial <;> simp only [ite_true, Bool.false_eq_true, ite_false] at cx
    · rw [cx]
      exact ⟨lt.le, le_rfl⟩
    · rw [cx]
      exact ⟨le_rfl, lt.le⟩
  have sep (x : ℝ) (hx : x ∈ Set.Ioo (c i.castSucc) (c i.succ)) : f x ≠ g x := by
    intro same
    have h : x ∈ Set.range c := crossing.symm.subset ⟨incl i (Set.Ioo_subset_Icc_self hx), same⟩
    obtain ⟨j, rfl⟩ := h
    have lo := c.strictMono.lt_iff_lt.mp hx.1
    have hi := c.strictMono.lt_iff_lt.mp hx.2
    change i.val < j.val at lo
    change j.val < i.val + 1 at hi
    omega
  have signed := K.graphLensSign_mul_regionalAngleExcess_eq_endpoint hf hg (jordan i)
    ((included i).trans inside) (aligned i) w w_in initial cx forward_u forward_v on_bank on_close sep
    (c.strictMono Fin.castSucc_lt_succ) slopes tangent
    (local_rays.mono (fun _ h hit => h (included i hit))) ref active
  cases initial
  · have w_end : K.projectedVertex w 0 = b := congrArg (fun z : Plane => z 0) at_w
    rw [K.graph_regionDifference_eq_lastLens hf hg c first last crossing jordan aligned
      sample sample_in sample_off w w_end]
    exact signed
  · have w_start : K.projectedVertex w 0 = a := congrArg (fun z : Plane => z 0) at_w
    rw [K.graph_regionDifference_eq_firstLens hf hg c first last crossing jordan aligned
      sample sample_in sample_off w w_start]
    exact signed

end Unfoldings.ConvexRoof
