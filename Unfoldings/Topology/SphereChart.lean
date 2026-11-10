module

public import Mathlib.Geometry.Manifold.Instances.Sphere

/-! A punctured unit sphere has an explicit Euclidean homeomorphism. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def spherePunctureHomeomorph (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (pole : Metric.sphere (0 : E) 1) :
    ↥(({pole} : Set (Metric.sphere (0 : E) 1))ᶜ) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (Homeomorph.setCongr (stereographic'_source (n := n) pole).symm).trans
    ((stereographic' n pole).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target (n := n) pole)).trans
        (Homeomorph.Set.univ _)))

end Unfoldings
