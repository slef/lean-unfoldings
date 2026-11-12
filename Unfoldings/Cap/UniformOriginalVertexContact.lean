module

public import Unfoldings.Cap.UniformOriginalClosedContact
public import Unfoldings.Cap.ClosedFaceVertexContact

/-! Uniform reduction of foreign contacts to original vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

theorem exists_uniform_original_sector_vertex_contact_reduction
    (t : ℝ) (positive : 0 < t) (small : t < 1) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ {origin : C.Vertex Set.univ} (M : K.SectorForest t origin),
          ¬ C.IsBoundaryVertex Set.univ origin →
          0 < K.roofHeight (K.projectedVertex origin) →
          ∀ E : FacewiseDevelopment C M.retain, ∀ f g (p q : Plane),
            p ∈ (K.projectedTriangle f).carrier → q ∈ (K.projectedTriangle g).carrier →
            E.projectedPlacement K f p = E.projectedPlacement K g q →
              p = q ∨ (K.projectedTriangle f).IsVertex p ∨ (K.projectedTriangle g).IsVertex q := by
  obtain ⟨φ, bounds, construct⟩ :=
    exists_uniform_original_sector_closed_contact.{u, v} t positive small
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt origin M internal source_height E f g p q first last same
  by_cases equal : p = q
  · exact Or.inl equal
  obtain ⟨center, exception, finite, contacts⟩ := construct K tilt M internal source_height E
  apply Or.inr
  apply E.isVertex_or_isVertex_of_foreign_projected_contact K isOpen_univ convex_univ center
    finite (fun a b x y hx hy => contacts a b x y hx.1 hy.1) f g
    ⟨first, Set.mem_univ p⟩ ⟨last, Set.mem_univ q⟩ equal same

end Unfoldings.ConvexCap
