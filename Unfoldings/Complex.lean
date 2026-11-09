module

public import Unfoldings.Geometry.Triangle
public import Unfoldings.Metric.Gluing

/-!
# Finite triangle complexes and their cut metrics

Each seam identifies two entire edge subspaces by an isometric equivalence.
There are no empty or partial overlap parameters. Manifold conditions, vertex
links, and exactness of the metric quotient are separate future theorems.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

universe u v

/-- A local edge of one triangular face. -/
structure EdgeRef (Face : Type u) where
  face : Face
  edge : Fin 3
  deriving DecidableEq

/-- Finite Euclidean cells with full-edge pairings. This need not be a manifold. -/
structure TriangleComplex (Face : Type u) [Fintype Face] where
  triangle : Face → Triangle
  Seam : Type v
  [finiteSeam : Fintype Seam]
  left : Seam → EdgeRef Face
  right : Seam → EdgeRef Face
  distinct : ∀ s, left s ≠ right s
  identify : ∀ s, (triangle (left s).face).Edge (left s).edge ≃ᵢ
    (triangle (right s).face).Edge (right s).edge
  /-- A local edge belongs to at most one pairing. -/
  unique : ∀ s t, left s = left t ∨ left s = right t ∨
    right s = left t ∨ right s = right t → s = t

attribute [instance] TriangleComplex.finiteSeam

namespace TriangleComplex

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

abbrev Cell (f : Face) : Type := (C.triangle f).Cell

abbrev Total := MetricGluing.Total C.Cell

/-- Retain the selected seams. The reverse transitions are supplied by the route construction. -/
def glue (retain : Set C.Seam) (a b : C.Total) : Prop :=
  ∃ s ∈ retain, ∃ x : (C.triangle (C.left s).face).Edge (C.left s).edge,
    a = ⟨(C.left s).face, (C.triangle (C.left s).face).edgeMap (C.left s).edge x⟩ ∧
    b = ⟨(C.right s).face,
      (C.triangle (C.right s).face).edgeMap (C.right s).edge (C.identify s x)⟩

/-- The constructed extended metric on the surface with only these seams retained. -/
abbrev Realization (retain : Set C.Seam) := MetricGluing.Realization C.Cell (C.glue retain)

/-- Each local cell maps canonically to the cut realization. -/
def faceMap (retain : Set C.Seam) (f : Face) : C.Cell f → C.Realization retain :=
  MetricGluing.of C.Cell (C.glue retain) f

theorem faceMap_lipschitz (retain : Set C.Seam) (f : Face) :
    LipschitzWith 1 (C.faceMap retain f) :=
  MetricGluing.of_lipschitz C.Cell (C.glue retain) f

theorem seam_identified (retain : Set C.Seam) (s : C.Seam) (hs : s ∈ retain)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge) :
    C.faceMap retain (C.left s).face ((C.triangle (C.left s).face).edgeMap (C.left s).edge x) =
    C.faceMap retain (C.right s).face
      ((C.triangle (C.right s).face).edgeMap (C.right s).edge (C.identify s x)) :=
  MetricGluing.point_eq_of_glue C.Cell ⟨s, hs, x, rfl, rfl⟩

theorem glue_mono {retain retain' : Set C.Seam} (inclusion : retain ⊆ retain') :
    ∀ a b, C.glue retain a b → C.glue retain' a b := by
  rintro a b ⟨s, hs, x, ha, hb⟩
  exact ⟨s, inclusion hs, x, ha, hb⟩

/-- Forget some cuts by restoring additional seams. -/
noncomputable def forgetCuts {retain retain' : Set C.Seam} (inclusion : retain ⊆ retain') :
    C.Realization retain → C.Realization retain' :=
  MetricGluing.forget C.Cell (C.glue_mono inclusion)

@[simp] theorem forgetCuts_faceMap {retain retain' : Set C.Seam} (inclusion : retain ⊆ retain')
    (f : Face) (x : C.Cell f) :
    C.forgetCuts inclusion (C.faceMap retain f x) = C.faceMap retain' f x := rfl

/-- Cutting cannot shorten distances: the map restoring seams is nonexpanding. -/
theorem forgetCuts_lipschitz {retain retain' : Set C.Seam} (inclusion : retain ⊆ retain') :
    LipschitzWith 1 (C.forgetCuts inclusion) :=
  MetricGluing.forget_lipschitz C.Cell (C.glue_mono inclusion)

end TriangleComplex
end Unfoldings
