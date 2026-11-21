module

public import Unfoldings.Polyhedron.GaussianIncidentHull
public import Unfoldings.Polyhedron.GaussianExtremeCells
public import Unfoldings.Polyhedron.GaussianOrderedArcs

/-! The link at an extreme vertex has a genuine change of outward normal. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open Cap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)
  {a : C.Vertex Set.univ} {n : ℕ}
  (c : (C.linkSystem Set.univ a).Chain n)

include P in
theorem exists_ne_linkNormals_of_extreme
    (covers : ∀ p, c.Visited p)
    (extreme : (F.gaussianSiteOfVertex a : Space) ∈ F.vertexHull.extremePoints ℝ) :
    ∃ i j : Fin (n + 1), linkNormals N c i ≠ linkNormals N c j := by
  classical
  by_contra constant
  push Not at constant
  let f := c.first.val.1.1
  let j := c.first.val.1.2
  have at_a : C.vertexOfCorner Set.univ (f, j) = a := c.first.property
  have normals (g : Face) (k : Fin 3) (at_g : C.vertexOfCorner Set.univ (g, k) = a) :
      N.normal g = N.normal f := by
    obtain ⟨i, hi⟩ := (C.linkCornerEquiv Set.univ a c covers).surjective ⟨(g, k), at_g⟩
    have eq := congrArg (fun p : C.CornerAt Set.univ a => p.val.1) hi
    exact (congrArg N.normal eq).symm.trans (constant i 0)
  let A := F.gaussianSiteOfVertex a
  let body := F.gaussianCell A
  obtain ⟨center, center_unit, hemisphere, hull⟩ := P.exists_gaussianCell_eq_incidentHull N a
  obtain ⟨z, hz, strict, _⟩ := F.exists_strict_gaussianCell_center P A extreme
  let L := northFrame center
  let slope (x : Space) := ((L x) 2)⁻¹ • horizontal (L x)
  have lift (x : Space) (hx : x ∈ body) : gnomonicNormal (slope x) = L x := by
    apply gnomonicNormal_slope
    · rw [L.norm_map]
      simpa only [Metric.mem_sphere, dist_zero_right] using hx.2
    · change 0 < northFrame center x 2
      rw [northFrame_height center center_unit]
      exact hemisphere x hx
  have z_slope : slope z ∈ convexHull ℝ (incidentGaussianSlopes N center a) := by
    rw [← hull]
    change gnomonicNormal (slope z) ∈ L '' body
    rw [lift z hz]
    exact Set.mem_image_of_mem L hz
  have slopes_eq : incidentGaussianSlopes N center a ⊆ {slope (N.normal f)} := by
    rintro u ⟨g, k, at_g, rfl⟩
    change slope (N.normal g) ∈ ({slope (N.normal f)} : Set Plane)
    rw [normals g k at_g]
    exact Set.mem_singleton _
  have slope_eq : slope z = slope (N.normal f) := by
    have h := convexHull_mono slopes_eq z_slope
    rw [convexHull_singleton] at h
    exact h
  have f_mem : N.normal f ∈ body :=
    Eq.mp (congrArg (fun u => N.normal f ∈ F.gaussianCell (F.gaussianSiteOfVertex u)) at_a)
      (F.normal_mem_gaussianCell_of_corner N f j)
  have same : z = N.normal f := by
    apply L.injective
    rw [← lift z hz, slope_eq, lift _ f_mem]
  let b := C.vertexOfCorner Set.univ (f, Triangle.next j)
  let B := F.gaussianSiteOfVertex b
  have valueA : (A : Space) = F.place f ((C.triangle f).vertex j) := by
    change F.toSpace Set.univ (C.vertexPoint Set.univ a) = _
    rw [← at_a, F.toSpace_vertexOfCorner]
  have valueB : (B : Space) = F.place f ((C.triangle f).vertex (Triangle.next j)) :=
    F.toSpace_vertexOfCorner f (Triangle.next j)
  have BA : B ≠ A := fun h =>
    (F.place f).injective.ne ((C.triangle f).edge_endpoints_ne j)
      (valueA.symm.trans ((congrArg Subtype.val h).symm.trans valueB))
  have lt : inner ℝ z (B : Space) < inner ℝ z (A : Space) := by
    apply (mem_interior_finiteHullNormalCone_iff Subtype.val_injective A).mp strict B BA
  rw [same, valueA, valueB] at lt
  have planeA := N.on_plane f ((C.triangle f).vertex j)
  have planeB := N.on_plane f ((C.triangle f).vertex (Triangle.next j))
  rw [inner_sub_right] at planeA planeB
  linarith only [lt, planeA, planeB]

include P in
theorem nonempty_cyclicRunStarts_of_extreme
    (covers : ∀ p, c.Visited p)
    (extreme : (F.gaussianSiteOfVertex a : Space) ∈ F.vertexHull.extremePoints ℝ) :
    (cyclicRunStarts (linkNormals N c)).Nonempty := by
  obtain ⟨i, j, different⟩ := P.exists_ne_linkNormals_of_extreme N c covers extreme
  obtain ⟨k, h, prev⟩ := exists_cyclic_label_entry (linkNormals N c) (linkNormals N c i)
    ⟨i, rfl⟩ ⟨j, Ne.symm different⟩
  exact ⟨k, (mem_cyclicRunStarts _ _).mpr (fun eq => prev (eq.trans h))⟩

end Unfoldings.SpatialFolding.ConvexBoundary
