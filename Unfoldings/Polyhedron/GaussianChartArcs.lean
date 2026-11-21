module

public import Unfoldings.Polyhedron.GaussianBoundaryCycle
public import Unfoldings.Polyhedron.GaussianExactFrontier

/-! The simple normal cycle gives an ordered family of actual stereographic boundary arcs. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open Cap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)
  {a : C.Vertex Set.univ} {n : ℕ} (c : (C.linkSystem Set.univ a).Chain n)
  (closes : C.linkMate Set.univ a (C.linkTurn Set.univ a c.last) = c.first)
  (covers : ∀ p, c.Visited p)
  {m : ℕ} (count : (cyclicRunStarts (linkNormals N c)).card = m + 1)

include P closes covers in
/-- The projected genuine arcs lie on the strictly centered chart frontier.
Every compressed normal projects to a distinct vertex, and an arc contains
only its two vertex endpoints among these vertices. -/
theorem compressedLinkNormal_chart_arcs
    (extreme : (F.gaussianSiteOfVertex a : Space) ∈ F.vertexHull.extremePoints ℝ)
    (q : Space) (center : q ∈ F.gaussianCell (F.gaussianSiteOfVertex a))
    (strict : q ∈ interior (F.gaussianCone (F.gaussianSiteOfVertex a)))
    (hemisphere : ∀ z ∈ F.gaussianCell (F.gaussianSiteOfVertex a), 0 < inner ℝ q z) :
    let p := compressedLinkNormal N c count
    let project := stereographicCoord ∘ northFrame q
    let arc (i : Fin (m + 1)) := project '' closedMinorArc (p i) (p (finRotate (m + 1) i))
    Function.Injective (project ∘ p) ∧
      (∀ i, arc i ⊆ frontier (F.gaussianChartRegion (F.gaussianSiteOfVertex a) q)) ∧
      (∀ i, IsPreconnected (arc i)) ∧
      ∀ i j, project (p j) ∈ arc i ↔ j = i ∨ j = finRotate (m + 1) i := by
  classical
  let p := compressedLinkNormal N c count
  let proj := stereographicCoord ∘ northFrame q
  let next := finRotate (m + 1)
  let L := northFrame q
  let cell := F.gaussianCell (F.gaussianSiteOfVertex a)
  let K := F.gaussianChartRegion (F.gaussianSiteOfVertex a) q
  let A (i : Fin (m + 1)) := closedMinorArc (p i) (p (next i))
  let s := P.runStartGaussianSeamEquiv N c closes covers count
  let start := cyclicRunStart (linkNormals N c) count
  have ends (i : Fin (m + 1)) : HasGaussianArcEnds N (s (next i)).val (p i) (p (next i)) := by
    have h := P.compressedLinkNormal_arcEnds N c closes covers count (next i)
    change HasGaussianArcEnds N (s (next i)).val (p (next.symm (next i))) (p (next i)) at h
    rwa [next.symm_apply_apply] at h
  have arc_eq (i : Fin (m + 1)) :
      closedMinorArc (N.normal (C.left (s (next i)).val).face)
        (N.normal (C.right (s (next i)).val).face) = A i := (ends i).closedMinorArc
  have link (i : Fin (m + 1)) :
      ∃ b : C.Vertex Set.univ, C.seamGraph.IsLink (s (next i)).val a b := by
    obtain ⟨b, across, _⟩ :=
      P.exists_linked_vertex_of_germDirection (c.point (start (next i)))
    exact ⟨b, across⟩
  have on_frontier (i : Fin (m + 1)) : L '' A i ⊆ inverseStereographic '' frontier K := by
    rw [P.inverseStereographic_image_gaussianChart_frontier N a center strict hemisphere]
    apply Set.image_mono
    let si := (s (next i)).val
    have included : si ∈ incidentSeams a := (Finset.mem_filter.mp (s (next i)).property).1
    let t : {s : C.Seam // a = C.seamVertex s false ∨ a = C.seamVertex s true} :=
      ⟨si, (Finset.mem_filter.mp included).2⟩
    rw [← arc_eq i]
    intro z hz
    exact Set.mem_iUnion.mpr ⟨t, hz⟩
  have arc_in (i : Fin (m + 1)) : A i ⊆ cell := by
    intro z hz
    have hz' := on_frontier i (Set.mem_image_of_mem L hz)
    have cell_image := (F.gaussianChartRegion_properties (F.gaussianSiteOfVertex a) center
      hemisphere).2.2.2.2
    have in_image : L z ∈ L '' cell := by
      rw [← cell_image]
      have closed : IsClosed K := (F.gaussianChartRegion_properties _ center hemisphere).1.isClosed
      exact Set.image_mono closed.frontier_subset hz'
    exact L.injective.mem_set_image.mp in_image
  have p_in (i : Fin (m + 1)) : p i ∈ cell := arc_in i (Set.mem_insert _ _)
  have inv (z : Space) (hz : z ∈ cell) : inverseStereographic (proj z) = L z := by
    have unit : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hz.2
    have q_unit : ‖q‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using center.2
    have pos : 0 < L z 2 := by
      change 0 < northFrame q z 2
      rw [northFrame_height q q_unit]
      exact hemisphere _ hz
    exact inverseStereographic_stereographicCoord ((L.norm_map z).trans unit) (by linarith)
  have proj_in (i : Fin (m + 1)) : proj '' A i ⊆ frontier K := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨x, hx, h⟩ := on_frontier i (Set.mem_image_of_mem L hz)
    have eq := congrArg stereographicCoord h
    rw [stereographicCoord_inverseStereographic] at eq
    change stereographicCoord (L z) ∈ frontier K
    exact eq ▸ hx
  have connected (i : Fin (m + 1)) : IsPreconnected (proj '' A i) := by
    have unit (j : Fin (m + 1)) : ‖p j‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using (p_in j).2
    have not_opposite : p i + p (next i) ≠ 0 := by
      intro zero
      have both := congrArg (fun z => inner ℝ q z) zero
      rw [inner_add_right, inner_zero_right] at both
      exact (add_pos (hemisphere _ (p_in i)) (hemisphere _ (p_in (next i)))).ne' both
    apply (isPreconnected_closedMinorArc (unit i) (unit (next i)) not_opposite).image
    let height (z : Space) := 1 + L z 2
    have height_cont : Continuous height :=
      continuous_const.add
        ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2).continuous.comp L.continuous)
    have nonzero (z : Space) (hz : z ∈ A i) : height z ≠ 0 := by
      have q_unit : ‖q‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using center.2
      have up : 0 < northFrame q z 2 := by
        rw [northFrame_height q q_unit]
        exact hemisphere _ (arc_in i hz)
      change 1 + northFrame q z 2 ≠ 0
      linarith
    change ContinuousOn (fun z => (height z)⁻¹ • horizontal (L z)) (A i)
    exact (height_cont.continuousOn.inv₀ nonzero).smul
      (horizontalCLM.continuous.comp L.continuous).continuousOn
  have pinj : Function.Injective p :=
    P.compressedLinkNormal_injective N c closes covers count extreme
  have project_inj {x y : Space} (hx : x ∈ cell) (hy : y ∈ cell)
      (same : proj x = proj y) : x = y := by
    apply L.injective
    rw [← inv x hx, ← inv y hy, same]
  refine ⟨fun i j same => pinj (project_inj (p_in i) (p_in j) same), proj_in, connected, ?_⟩
  intro i j
  constructor
  · rintro ⟨z, hz, equal⟩
    have eq := project_inj (arc_in i hz) (p_in j) equal
    rw [eq] at hz
    rcases Set.mem_insert_iff.mp hz with same | rest
    · exact Or.inl (pinj same)
    rcases Set.mem_insert_iff.mp rest with same | inside
    · exact Or.inr (pinj same)
    obtain ⟨b, physical⟩ := link i
    have such : p j ∈ Set.range (linkNormals N c ∘ cyclicRunStart (linkNormals N c) count) :=
      ⟨j, rfl⟩
    rw [range_compressed_linkNormals N c covers count] at such
    obtain ⟨f, k, at_a, normal⟩ := such
    have genuine := (Finset.mem_filter.mp (s (next i)).property).2
    apply (P.face_normal_not_mem_open_dual_arc N physical genuine f k at_a).elim
    rwa [(ends i).openMinorArc, normal]
  · rintro (rfl | rfl)
    · exact Set.mem_image_of_mem _ (Set.mem_insert _ _)
    · exact Set.mem_image_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

end Unfoldings.SpatialFolding.ConvexBoundary
