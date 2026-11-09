module

public import Unfoldings.Complex
public import Unfoldings.Geometry.Separation

/-!
# Developments that may overlap

Every face is placed once by a planar rigid motion. A retained seam agrees
pointwise and its two faces lie on opposite sides. No tree, disk topology, or
global injectivity is required. Local injectivity at uncut vertices is also a
separate condition: the facewise interface does not rule out branched vertices.
-/

@[expose] public section

namespace Unfoldings

universe u v

variable {Face : Type u} [Fintype Face]

/-- A facewise development with the correct local opening across every retained seam. -/
structure FacewiseDevelopment (C : TriangleComplex.{u, v} Face) (retain : Set C.Seam) where
  place : Face → Plane ≃ᵃⁱ[ℝ] Plane
  joined : ∀ s ∈ retain, ∀ x : (C.triangle (C.left s).face).Edge (C.left s).edge,
    place (C.left s).face x = place (C.right s).face (C.identify s x)
  opposite : ∀ s ∈ retain,
    let a := place (C.left s).face ((C.triangle (C.left s).face).vertex (C.left s).edge)
    let b := place (C.left s).face
      ((C.triangle (C.left s).face).vertex (Triangle.next (C.left s).edge))
    orient a b (place (C.left s).face ((C.triangle (C.left s).face).opposite (C.left s).edge)) *
      orient a b (place (C.right s).face
        ((C.triangle (C.right s).face).opposite (C.right s).edge)) < 0

namespace FacewiseDevelopment

variable {C : TriangleComplex.{u, v} Face} {retain : Set C.Seam}
  (D : FacewiseDevelopment C retain)

/-- The rigid face placements agree on the declared seam relation. -/
theorem compatible : ∀ a b, C.glue retain a b →
    D.place a.1 a.2 = D.place b.1 b.2 := by
  rintro a b ⟨s, hs, x, rfl, rfl⟩
  exact D.joined s hs x

theorem face_lipschitz (f : Face) :
    LipschitzWith 1 (fun x : C.Cell f => D.place f (x : Plane)) :=
  LipschitzWith.of_edist_le fun x y => ((D.place f).isometry x y).le

/-- A development descends to the actual cut metric realization, even when it overlaps. -/
noncomputable def toPlane : C.Realization retain → Plane :=
  MetricGluing.lift C.Cell (C.glue retain)
    (fun f x => D.place f (x : Plane)) D.face_lipschitz D.compatible

@[simp] theorem toPlane_faceMap (f : Face) (x : C.Cell f) :
    D.toPlane (C.faceMap retain f x) = D.place f (x : Plane) := rfl

/-- Planar chords can be shorter than intrinsic paths; global equality is not required. -/
theorem toPlane_lipschitz : LipschitzWith 1 D.toPlane :=
  MetricGluing.lift_lipschitz C.Cell (C.glue retain)
    (fun f x => D.place f (x : Plane)) D.face_lipschitz D.compatible

include D in
/-- The existence of a consistent rigid development rules out shortcuts within one face.
This strengthens unconditional nonexpansion only after the development is supplied. -/
theorem faceMap_isometry (f : Face) : Isometry (C.faceMap retain f) := by
  intro x y
  apply le_antisymm (MetricGluing.edist_of_le C.Cell (C.glue retain) f x y)
  have bound := D.toPlane_lipschitz.edist_le_mul
    (C.faceMap retain f x) (C.faceMap retain f y)
  calc
    edist x y = edist (D.place f (x : Plane)) (D.place f (y : Plane)) :=
      ((D.place f).isometry x y).symm
    _ ≤ edist (C.faceMap retain f x) (C.faceMap retain f y) := by simpa using bound

/-- The whole closed image of one original triangular cell. -/
def faceImage (f : Face) : Set Plane := D.place f '' (C.triangle f).carrier

/-- Distinct face interiors are disjoint; boundary contacts are permitted. -/
def Nonoverlapping : Prop :=
  ∀ f g, f ≠ g → Disjoint (interior (D.faceImage f)) (interior (D.faceImage g))

/-- Count original face interiors, not boundary copies or auxiliary triangles. -/
noncomputable def multiplicity (x : Plane) : ℕ := by
  classical
  exact (Finset.univ.filter fun f => x ∈ interior (D.faceImage f)).card

theorem nonoverlapping_iff_multiplicity_le_one :
    D.Nonoverlapping ↔ ∀ x, D.multiplicity x ≤ 1 := by
  classical
  constructor
  · intro nonoverlap x
    apply Finset.card_le_one.mpr
    intro f hf g hg
    by_contra different
    exact Set.disjoint_left.mp (nonoverlap f g different)
      (Finset.mem_filter.mp hf).2 (Finset.mem_filter.mp hg).2
  · intro bound f g different
    apply Set.disjoint_left.mpr
    intro x hx hy
    have same := Finset.card_le_one.mp (bound x)
      f (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hx⟩)
      g (Finset.mem_filter.mpr ⟨Finset.mem_univ g, hy⟩)
    exact different same

/-- Original-corner separator certificates suffice for the whole developed cells. -/
theorem nonoverlapping_of_vertex_separators
    (separate : ∀ f g, f ≠ g → ∃ height : Plane →L[ℝ] ℝ,
      Function.Surjective height ∧ ∃ level : ℝ,
      (∀ i, height (D.place f ((C.triangle f).vertex i)) ≤ level) ∧
      (∀ i, level ≤ height (D.place g ((C.triangle g).vertex i)))) :
    D.Nonoverlapping := by
  intro f g different
  obtain ⟨height, surjective, level, upper, lower⟩ := separate f g different
  exact (C.triangle f).disjoint_interiors_of_vertex_separator (C.triangle g)
    (D.place f).toAffineEquiv.toAffineMap (D.place g).toAffineEquiv.toAffineMap
    height surjective level upper lower

end FacewiseDevelopment
end Unfoldings
