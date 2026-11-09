module

public import Unfoldings.Basic
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Injectivity from radial lifts

This isolates the nonoverlap argument behind source unfolding. It assumes the
actual radial paths and local injectivity; it does not assert their existence
for a polyhedron. No completeness, covering-map theorem or cut-locus theory is
needed for uniqueness of these already existing lifts.
-/

@[expose] public section

namespace Unfoldings

/-- A locally injective development with a radial path to every point is injective.
Apply this on the regular retained interior; boundary copies need not be injective. -/
theorem injective_of_radial_paths {X : Type*} [TopologicalSpace X] [T2Space X]
    (develop : X → Plane) (local_injective : IsLocallyInjective develop) (source : X)
    (radial : ∀ x, Path source x)
    (straight : ∀ x t, develop (radial x t) =
      AffineMap.lineMap (develop source) (develop x) (t : ℝ)) :
    Function.Injective develop := by
  intro x y equal
  have same_image : develop ∘ radial x = develop ∘ radial y := by
    funext t
    change develop (radial x t) = develop (radial y t)
    rw [straight, straight, equal]
  have same_path := (T2Space.isSeparatedMap develop).eq_of_comp_eq local_injective
    (radial x).continuous (radial y).continuous same_image (0 : unitInterval)
    ((radial x).source.trans (radial y).source.symm)
  simpa only [Path.target] using congrFun same_path (1 : unitInterval)

/-- The local-homeomorphism form used for a developing map on a flat surface. -/
theorem injective_of_radial_paths_of_local_homeomorph {X : Type*}
    [TopologicalSpace X] [T2Space X] {develop : X → Plane}
    (local_homeomorph : IsLocalHomeomorph develop) (source : X)
    (radial : ∀ x, Path source x)
    (straight : ∀ x t, develop (radial x t) =
      AffineMap.lineMap (develop source) (develop x) (t : ℝ)) :
    Function.Injective develop :=
  Unfoldings.injective_of_radial_paths develop local_homeomorph.isLocallyInjective
    source radial straight

end Unfoldings
