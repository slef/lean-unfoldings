module

public import Unfoldings.Examples.Pyramid.Complex
public import Unfoldings.Examples.Pyramid.Projection
public import Unfoldings.Complex.ProjectedEmbedding

/-! Exact projected geometric contacts are precisely the pyramid's declared radial seam chains. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Examples.Pyramid

theorem projected_pairs_complete (f g : Bool × Bool) (different : f ≠ g) (e d : Fin 3)
    (same : (projectedTriangle f).edge e = (projectedTriangle g).edge d) :
    ∃ s, (complex.left s = ⟨f, e⟩ ∧ complex.right s = ⟨g, d⟩) ∨
      (complex.left s = ⟨g, d⟩ ∧ complex.right s = ⟨f, e⟩) := by
  fin_cases e
  · let h := (f.1, !f.2)
    have not_same : f ≠ h := by
      obtain ⟨a, b⟩ := f
      cases a <;> cases b <;> decide
    have pair := TriangleFamily.edge_partner_unique projectedTriangle projected_separated
      (a := ⟨f, 0⟩) (b := ⟨g, d⟩) (c := ⟨h, 0⟩) different not_same same (by rfl)
    have faces := congrArg EdgeRef.face pair
    have edges := congrArg EdgeRef.edge pair
    change g = h at faces
    change d = 0 at edges
    rw [faces, edges]
    refine ⟨(false, f.1), ?_⟩
    obtain ⟨a, b⟩ := f
    cases b <;> simp [complex, left, right, h]
  · let m := vec2 (sign f.1 / 2) (sign f.2 / 2)
    have at_edge : m ∈ (projectedTriangle f).edge 1 := by
      change m ∈ segment ℝ (vec2 (sign f.1) 0) (vec2 0 (sign f.2))
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      ext i
      fin_cases i <;> simp [m, vec2] <;> ring
    have in_g := (projectedTriangle g).edge_subset d (same ▸ at_edge)
    have bounds := (mem_carrier g m).mp in_g
    have equal : f = g := by
      obtain ⟨a, b⟩ := f
      obtain ⟨c, d⟩ := g
      cases a <;> cases b <;> cases c <;> cases d <;> simp_all [sign, m, vec2] <;> norm_num at *
    exact (different equal).elim
  · let h := (!f.1, f.2)
    have not_same : f ≠ h := by
      obtain ⟨a, b⟩ := f
      cases a <;> cases b <;> decide
    have pair := TriangleFamily.edge_partner_unique projectedTriangle projected_separated
      (a := ⟨f, 2⟩) (b := ⟨g, d⟩) (c := ⟨h, 2⟩) different not_same same (by rfl)
    have faces := congrArg EdgeRef.face pair
    have edges := congrArg EdgeRef.edge pair
    change g = h at faces
    change d = 2 at edges
    rw [faces, edges]
    refine ⟨(true, f.2), ?_⟩
    obtain ⟨a, b⟩ := f
    cases a <;> simp [complex, left, right, h]

theorem projected_family : complex.affineProjectedTriangle projection = projectedTriangle := by
  funext f
  apply Triangle.eq_of_vertex_eq
  intro i
  exact triangle.cornerEquiv_vertex (projectedTriangle f) i

theorem joined_projection (s : complex.Seam)
    (x : (complex.triangle (complex.left s).face).Edge (complex.left s).edge) :
    projection (complex.left s).face x.val =
      projection (complex.right s).face (complex.identify s x).val := by
  rw [projection_placement, projection_placement]
  exact congrArg Cap.horizontal (folding.joined s x)

/-- The full intrinsic pyramid embeds by vertical projection onto the closed diamond. -/
theorem projection_injective : Function.Injective
    (fun x : complex.Realization Set.univ => Cap.horizontal (folding.toSpace Set.univ x)) := by
  intro x y same
  obtain ⟨a, rfl⟩ := MetricGluing.point_surjective complex.Cell (complex.glue Set.univ) x
  obtain ⟨b, rfl⟩ := MetricGluing.point_surjective complex.Cell (complex.glue Set.univ) y
  have convex : Convex ℝ (⋃ f, (complex.affineProjectedTriangle projection f).carrier) := by
    rw [projected_family, projected_cover]
    exact convex_domain
  have conforming : TriangleFamily.Conforming (complex.affineProjectedTriangle projection) := by
    rw [projected_family]
    exact projected_conforming
  have separated : Pairwise (fun f g => Disjoint
      (interior (complex.affineProjectedTriangle projection f).carrier)
      (interior (complex.affineProjectedTriangle projection g).carrier)) := by
    rw [projected_family]
    exact projected_separated
  have complete : ∀ f g : Bool × Bool, f ≠ g → ∀ e d : Fin 3,
      (complex.affineProjectedTriangle projection f).edge e =
        (complex.affineProjectedTriangle projection g).edge d →
        ∃ s, (complex.left s = ⟨f, e⟩ ∧ complex.right s = ⟨g, d⟩) ∨
          (complex.left s = ⟨g, d⟩ ∧ complex.right s = ⟨f, e⟩) := by
    rw [projected_family]
    exact projected_pairs_complete
  have physical : projection a.1 a.2.val = projection b.1 b.2.val := by
    rw [projection_placement, projection_placement]
    exact same
  exact (complex.point_eq_iff Set.univ a b).mpr
    (complex.related_of_affine_projection_eq projection joined_projection convex conforming
      separated complete a b physical)

end Unfoldings.Examples.Pyramid
