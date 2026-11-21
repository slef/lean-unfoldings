module

public import Unfoldings.Polyhedron.GaussianOrderedArcs
public import Unfoldings.Polyhedron.FigureSupportChordAngle
public import Unfoldings.Polyhedron.AngularLink

/-! The exterior angle between consecutive genuine Gaussian sides is at least
the minimum original triangle angle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open InnerProductGeometry

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)
  {a : C.Vertex Set.univ}

theorem exists_linked_vertex_of_germDirection (p : C.LinkGerm Set.univ a) :
    ∃ b : C.Vertex Set.univ, C.seamGraph.IsLink (P.germSeam p.val) a b ∧
      F.germDirection p.val =
        (F.gaussianSiteOfVertex b : Space) - (F.gaussianSiteOfVertex a : Space) := by
  let s := P.germSeam p.val
  obtain ⟨bank, hg⟩ := P.exists_germSeam_side p.val
  let e := C.seamSide s bank
  let flag := p.val.2
  let b := C.vertexOfCorner Set.univ (C.germOfEndpoint e (!flag)).1
  have start : C.vertexOfCorner Set.univ (C.germOfEndpoint e flag).1 = a :=
    (congrArg (fun g : C.Germ => C.vertexOfCorner Set.univ g.1) hg).symm.trans p.property
  refine ⟨b, ?_, ?_⟩
  · have actual := C.seamGraph_side_link s bank
    cases sides : flag
    · have first : C.vertexOfCorner Set.univ (C.germOfEndpoint e false).1 = a := by
        simpa only [sides] using start
      rw [show b = C.vertexOfCorner Set.univ (C.germOfEndpoint e true).1 by
        simp only [b, sides, Bool.not_false]]
      exact Eq.mp (congrArg (fun u => C.seamGraph.IsLink s u
        (C.vertexOfCorner Set.univ (C.germOfEndpoint e true).1)) first) actual
    · have first : C.vertexOfCorner Set.univ (C.germOfEndpoint e true).1 = a := by
        simpa only [sides] using start
      rw [show b = C.vertexOfCorner Set.univ (C.germOfEndpoint e false).1 by
        simp only [b, sides, Bool.not_true]]
      exact Eq.mp (congrArg (fun u => C.seamGraph.IsLink s u
        (C.vertexOfCorner Set.univ (C.germOfEndpoint e false).1)) first) actual.symm
  · have last := congrArg F.germFarPoint hg
    rw [F.germFarPoint_germOfEndpoint] at last
    have last_site : F.germFarPoint p.val = (F.gaussianSiteOfVertex b : Space) := by
      change _ = F.toSpace Set.univ (C.vertexPoint Set.univ b)
      change _ = F.toSpace Set.univ
        (C.vertexPoint Set.univ (C.vertexOfCorner Set.univ (C.germOfEndpoint e (!flag)).1))
      rw [F.toSpace_vertexOfCorner]
      have endpoint (t : Bool) :
          F.place (C.germOfEndpoint e t).1.1
              ((C.triangle (C.germOfEndpoint e t).1.1).vertex (C.germOfEndpoint e t).1.2) =
            F.place e.face ((C.triangle e.face).endpoint e.edge t).val := by
        cases t <;> rfl
      exact last.trans (endpoint (!flag)).symm
    unfold SpatialFolding.germDirection
    rw [last_site, F.linkGerm_apex Set.univ a p]
    rfl

private theorem normal_inner_germDirection_eq_zero (p : C.Germ) :
    inner ℝ (N.normal p.1.1) (F.germDirection p) = 0 := by
  obtain ⟨w, eq⟩ := F.germDirection_mem_range p
  rw [← eq]
  exact N.tangent _ _

variable {n : ℕ} (c : (C.linkSystem Set.univ a).Chain n)
  (closes : C.linkMate Set.univ a (C.linkTurn Set.univ a c.last) = c.first)
  (covers : ∀ p, c.Visited p)

include P in
/-- At a corner of the compressed normal cycle, the two adjacent original
seams bound a common supporting face sector. Their spherical inward normals
make at least the minimum angle of an input triangle. -/
theorem min_angle_le_of_adjacent_gaussian_supports
    (extreme : F.toSpace Set.univ (C.vertexPoint Set.univ a) ∈ F.vertexHull.extremePoints ℝ)
    {eta : ℝ} (min_angle : ∀ f i, eta ≤ (C.triangle f).cornerAngle i)
    {m : ℕ} (count : (cyclicRunStarts (linkNormals N c)).card = m + 1)
    (k : Fin (m + 1)) (not_fixed : finRotate (m + 1) k ≠ k) :
    let s := P.runStartGaussianSeamEquiv N c closes covers count
    ∃ b d : C.Vertex Set.univ,
      C.seamGraph.IsLink (s k).val a b ∧
      C.seamGraph.IsLink (s (finRotate (m + 1) k)).val a d ∧
      eta ≤ angle ((F.gaussianSiteOfVertex a : Space) - (F.gaussianSiteOfVertex b : Space))
        ((F.gaussianSiteOfVertex a : Space) - (F.gaussianSiteOfVertex d : Space)) := by
  let start := cyclicRunStart (linkNormals N c) count
  let i := start k
  let j := start (finRotate (m + 1) k)
  let p := c.point i
  let q := c.point j
  let f := p.val.1.1
  let V := P.vertexFigure a extreme
  have different : i ≠ j := fun h => not_fixed (start.injective h.symm)
  have at_f : inner ℝ (N.normal f)
      (F.toSpace Set.univ (C.vertexPoint Set.univ a) - F.place f 0) = 0 := by
    change inner ℝ (N.normal p.val.1.1)
      (F.toSpace Set.univ (C.vertexPoint Set.univ a) - F.place p.val.1.1 0) = 0
    rw [← F.linkGerm_apex Set.univ a p]
    exact N.on_plane _ _
  have prev := label_predecessor_cyclicRunStart (linkNormals N c) count k
  change N.normal (c.point ((finRotate (n + 1)).symm j)).val.1.1 = N.normal f at prev
  rw [← linkFace_mate_eq_prev c closes j] at prev
  have tangent_q : inner ℝ (N.normal f) (F.germDirection q.val) = 0 := by
    rw [← prev]
    change inner ℝ (N.normal (C.mateGerm Set.univ q.val).1.1) (F.germDirection q.val) = 0
    rw [← F.germDirection_mate Set.univ q.val]
    exact normal_inner_germDirection_eq_zero N _
  have bound := P.min_angle_le_of_link_rays_in_face_plane V c N closes covers min_angle i j
    different f at_f (normal_inner_germDirection_eq_zero N p.val) tangent_q
  obtain ⟨b, link_p, ray_p⟩ := P.exists_linked_vertex_of_germDirection p
  obtain ⟨d, link_q, ray_q⟩ := P.exists_linked_vertex_of_germDirection q
  refine ⟨b, d, link_p, link_q, ?_⟩
  change eta ≤ angle (F.germDirection p.val) (F.germDirection q.val) at bound
  rw [ray_p, ray_q, ← angle_neg_neg] at bound
  simpa only [neg_sub] using bound

end Unfoldings.SpatialFolding.ConvexBoundary
