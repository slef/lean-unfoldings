module

public import Unfoldings.Development
public import Unfoldings.Geometry.SharedEdgeMultiplicity
public import Mathlib.Data.Fintype.Powerset

/-!
# Canonical whole-edge pairings for a geometric triangle partition

Pair all equal whole geometric edges of different triangles. Disjoint triangle
interiors prove that no local edge can have two partners. The resulting actual
triangle complex has an identity planar development with strict opposite-side
opening. Conformity and a disk realization remain separate geometric results.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

instance EdgeRef.finite {Face : Type*} [Finite Face] : Finite (EdgeRef Face) :=
  Finite.of_injective (fun e : EdgeRef Face => (e.face, e.edge)) (by
    rintro ⟨f, e⟩ ⟨g, d⟩ equal
    cases equal
    rfl)

namespace TriangleFamily

variable {Face : Type*} (triangle : Face → Triangle)

local instance : DecidableEq (EdgeRef Face) := Classical.decEq _

def edgeCarrier (a : EdgeRef Face) : Set Plane := (triangle a.face).edge a.edge

/-- The partner of a fixed local edge is unique among triangles with disjoint interiors. -/
theorem edge_partner_unique
    (separated : Pairwise (fun f g =>
      Disjoint (interior (triangle f).carrier) (interior (triangle g).carrier)))
    {a b c : EdgeRef Face} (ab : a.face ≠ b.face) (ac : a.face ≠ c.face)
    (first : edgeCarrier triangle a = edgeCarrier triangle b)
    (last : edgeCarrier triangle a = edgeCarrier triangle c) : b = c := by
  by_cases same : b.face = c.face
  · have carriers : (triangle b.face).edge b.edge = (triangle b.face).edge c.edge := by
      exact first.symm.trans (last.trans (congrArg (fun f => (triangle f).edge c.edge) same.symm))
    have edges := (triangle b.face).edge_injective carriers
    cases b
    cases c
    cases same
    cases edges
    rfl
  · exact ((triangle a.face).not_three_shared_edges (triangle b.face) (triangle c.face)
      a.edge b.edge c.edge first last (separated ab) (separated ac) (separated same)).elim

structure SharedPair where
  first : EdgeRef Face
  last : EdgeRef Face
  different_faces : first.face ≠ last.face
  carrier_eq : edgeCarrier triangle first = edgeCarrier triangle last

abbrev GeometricSeam := {s : Finset (EdgeRef Face) //
  ∃ pair : SharedPair triangle, s = {pair.first, pair.last}}

def seamPair (s : GeometricSeam triangle) : SharedPair triangle := s.property.choose

theorem seamPair_labels (s : GeometricSeam triangle) :
    s.val = {(seamPair triangle s).first, (seamPair triangle s).last} := s.property.choose_spec

/-- The chosen orientation of an unordered seam is one of its two actual orientations. -/
theorem seamPair_eq_or_swap (s : GeometricSeam triangle) {a b : EdgeRef Face}
    (labels : s.val = {a, b}) :
    ((seamPair triangle s).first = a ∧ (seamPair triangle s).last = b) ∨
      ((seamPair triangle s).first = b ∧ (seamPair triangle s).last = a) := by
  have first : (seamPair triangle s).first ∈ ({a, b} : Finset _) := by
    rw [← labels, seamPair_labels]
    exact Finset.mem_insert_self _ _
  have last : (seamPair triangle s).last ∈ ({a, b} : Finset _) := by
    rw [← labels, seamPair_labels]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have different : (seamPair triangle s).first ≠ (seamPair triangle s).last :=
    fun equal => (seamPair triangle s).different_faces (congrArg EdgeRef.face equal)
  simp only [Finset.mem_insert, Finset.mem_singleton] at first last
  rcases first with first | first <;> rcases last with last | last
  · exact (different (first.trans last.symm)).elim
  · exact Or.inl ⟨first, last⟩
  · exact Or.inr ⟨first, last⟩
  · exact (different (first.trans last.symm)).elim

/-- Meeting at any local edge forces equality of the entire unordered seam label. -/
theorem sharedPair_eq_of_shared_edge
    (separated : Pairwise (fun f g =>
      Disjoint (interior (triangle f).carrier) (interior (triangle g).carrier)))
    (p q : SharedPair triangle)
    (same : p.first = q.first ∨ p.first = q.last ∨ p.last = q.first ∨ p.last = q.last) :
    ({p.first, p.last} : Finset (EdgeRef Face)) = {q.first, q.last} := by
  classical
  rcases same with first | first | last | last
  · have other : p.last = q.last := edge_partner_unique triangle separated p.different_faces
      (first.symm ▸ q.different_faces) p.carrier_eq (first.symm ▸ q.carrier_eq)
    rw [first, other]
  · have other : p.last = q.first := edge_partner_unique triangle separated p.different_faces
      (first.symm ▸ q.different_faces.symm) p.carrier_eq (first.symm ▸ q.carrier_eq.symm)
    rw [first, other, Finset.pair_comm]
  · have other : p.first = q.last := edge_partner_unique triangle separated p.different_faces.symm
      (last.symm ▸ q.different_faces) p.carrier_eq.symm (last.symm ▸ q.carrier_eq)
    rw [last, other, Finset.pair_comm]
  · have other : p.first = q.first := edge_partner_unique triangle separated p.different_faces.symm
      (last.symm ▸ q.different_faces.symm) p.carrier_eq.symm (last.symm ▸ q.carrier_eq.symm)
    rw [last, other]

/-- Construct all actual whole-edge seams, with uniqueness derived from geometric separation. -/
def pairedComplex
    [Fintype Face]
    (separated : Pairwise (fun f g =>
      Disjoint (interior (triangle f).carrier) (interior (triangle g).carrier))) :
    TriangleComplex Face where
  triangle := triangle
  Seam := GeometricSeam triangle
  finiteSeam := Fintype.ofFinite _
  left s := (seamPair triangle s).first
  right s := (seamPair triangle s).last
  distinct s := fun equal => (seamPair triangle s).different_faces (congrArg EdgeRef.face equal)
  identify s := (triangle (seamPair triangle s).first.face).sharedEdgeIdentification
    (triangle (seamPair triangle s).last.face) (seamPair triangle s).first.edge
    (seamPair triangle s).last.edge (seamPair triangle s).carrier_eq
  unique s t shared := by
    apply Subtype.ext
    rw [seamPair_labels, seamPair_labels]
    exact sharedPair_eq_of_shared_edge triangle separated _ _ shared

/-- The canonical planar placement agrees on every constructed seam and opens it correctly. -/
def pairedDevelopment
    [Fintype Face]
    (separated : Pairwise (fun f g =>
      Disjoint (interior (triangle f).carrier) (interior (triangle g).carrier))) :
    FacewiseDevelopment (pairedComplex triangle separated) Set.univ where
  place _ := AffineIsometryEquiv.refl ℝ Plane
  joined _ _ _ := rfl
  opposite s _ := (triangle (seamPair triangle s).first.face).opposite_of_shared_edge
    (triangle (seamPair triangle s).last.face) (seamPair triangle s).first.edge
    (seamPair triangle s).last.edge (seamPair triangle s).carrier_eq
    (separated (seamPair triangle s).different_faces)

/-- Every matching pair really appears in the constructed seam system. -/
theorem pairedComplex_complete [Fintype Face]
    (separated : Pairwise (fun f g =>
      Disjoint (interior (triangle f).carrier) (interior (triangle g).carrier)))
    {a b : EdgeRef Face} (different : a.face ≠ b.face)
    (same : edgeCarrier triangle a = edgeCarrier triangle b) :
    ∃ s : (pairedComplex triangle separated).Seam,
      ((pairedComplex triangle separated).left s = a ∧
        (pairedComplex triangle separated).right s = b) ∨
      ((pairedComplex triangle separated).left s = b ∧
        (pairedComplex triangle separated).right s = a) := by
  let p : SharedPair triangle := ⟨a, b, different, same⟩
  let s : GeometricSeam triangle := ⟨{a, b}, p, rfl⟩
  exact ⟨s, seamPair_eq_or_swap triangle s rfl⟩

/-- Separation of the geometric triangles proves nonoverlap of their identity development. -/
theorem pairedDevelopment_nonoverlapping [Fintype Face]
    (separated : Pairwise (fun f g =>
      Disjoint (interior (triangle f).carrier) (interior (triangle g).carrier))) :
    (pairedDevelopment triangle separated).Nonoverlapping := by
  intro f g different
  simpa only [FacewiseDevelopment.faceImage, pairedDevelopment,
    pairedComplex, AffineIsometryEquiv.coe_refl, Set.image_id] using separated different

end TriangleFamily
end Unfoldings
