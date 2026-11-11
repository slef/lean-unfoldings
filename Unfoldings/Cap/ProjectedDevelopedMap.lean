module

public import Unfoldings.Cap.DevelopmentOrientation
public import Mathlib.Topology.LocallyFinite

/-! An actual facewise development gives a continuous projected map away from its cut seams. -/

@[expose] public section

noncomputable section

namespace Unfoldings

namespace ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Keep the actual seam images, including their endpoints. -/
def projectedCutSet (retain : Set C.Seam) : Set Plane :=
  ⋃ s : C.Seam, ⋃ (_ : s ∉ retain),
    (K.projectedTriangle (C.left s).face).edge (C.left s).edge

theorem projectFace_eq_of_related {a b : C.Total}
    (related : Relation.EqvGen (C.glue Set.univ) a b) :
    K.projectFace a.1 a.2.val = K.projectFace b.1 b.2.val := by
  have equal := (C.faceMap_eq_iff Set.univ a.1 b.1 a.2 b.2).mpr related
  exact congrArg (fun x => Cap.horizontal (K.folding.toSpace Set.univ x)) equal

theorem cut_edgePoint_mem_projectedCutSet {retain : Set C.Seam} (s : C.Seam)
    (cut : s ∉ retain) (x : (C.triangle (C.left s).face).Edge (C.left s).edge) :
    K.projectFace (C.left s).face x.val ∈ K.projectedCutSet retain := by
  refine Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨cut, ?_⟩⟩
  rw [projectedTriangle, Triangle.affineImage_edge]
  exact ⟨x.val, x.property, rfl⟩

end ConvexCap

namespace FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

/-- Original surface identifications remain developed identifications off the actual cuts. -/
theorem place_eq_of_related_away_cuts {a b : C.Total}
    (related : Relation.EqvGen (C.glue Set.univ) a b)
    (outside : K.projectFace a.1 a.2.val ∉ K.projectedCutSet retain) :
    D.place a.1 a.2.val = D.place b.1 b.2.val := by
  induction related with
  | rel a b related =>
    obtain ⟨s, _, x, rfl, rfl⟩ := related
    by_cases kept : s ∈ retain
    · exact D.joined s kept x
    · exact (outside (K.cut_edgePoint_mem_projectedCutSet s kept x)).elim
  | refl a => rfl
  | symm a b related ih =>
    have avoid : K.projectFace a.1 a.2.val ∉ K.projectedCutSet retain := by
      rwa [K.projectFace_eq_of_related related]
    exact (ih avoid).symm
  | trans a b c first last ih₁ ih₂ =>
    have avoid : K.projectFace b.1 b.2.val ∉ K.projectedCutSet retain := by
      rwa [← K.projectFace_eq_of_related first]
    exact (ih₁ outside).trans (ih₂ avoid)

/-- Every projected face chart through an uncut point has the same actual developed value. -/
theorem projectedPlacement_eq_away_cuts {f g : Face} {p : Plane}
    (first : p ∈ (K.projectedTriangle f).carrier)
    (last : p ∈ (K.projectedTriangle g).carrier)
    (outside : p ∉ K.projectedCutSet retain) :
    D.projectedPlacement K f p = D.projectedPlacement K g p := by
  rw [ConvexCap.projectedTriangle, Triangle.affineImage_carrier] at first last
  obtain ⟨x, hx, first⟩ := first
  obtain ⟨y, hy, last⟩ := last
  have equal : C.faceMap Set.univ f ⟨x, hx⟩ = C.faceMap Set.univ g ⟨y, hy⟩ :=
    K.projection_injective (first.trans last.symm)
  have same := D.place_eq_of_related_away_cuts K
    ((C.faceMap_eq_iff Set.univ f g ⟨x, hx⟩ ⟨y, hy⟩).mp equal)
    (first.symm ▸ outside)
  calc
    _ = D.place f x := by rw [← first, D.projectedPlacement_apply]
    _ = D.place g y := same
    _ = D.projectedPlacement K g p := by rw [← last, D.projectedPlacement_apply]

open scoped Classical in
/-- Choose any containing face. Off the cut set the choice is immaterial. -/
def projectedMap (p : Plane) : Plane :=
  if member : p ∈ K.footprint then
    D.projectedPlacement K (Set.mem_iUnion.mp
      (K.footprint_eq_union_projectedTriangles.subset member)).choose p
  else 0

theorem projectedMap_eq {f : Face} {p : Plane}
    (member : p ∈ (K.projectedTriangle f).carrier)
    (outside : p ∉ K.projectedCutSet retain) :
    D.projectedMap K p = D.projectedPlacement K f p := by
  have footprint : p ∈ K.footprint :=
    K.footprint_eq_union_projectedTriangles.symm.subset (Set.mem_iUnion.mpr ⟨f, member⟩)
  simp only [projectedMap, dite_eq_left footprint]
  exact D.projectedPlacement_eq_away_cuts K
    (Set.mem_iUnion.mp (K.footprint_eq_union_projectedTriangles.subset footprint)).choose_spec
    member outside

/-- Finite closed-face gluing constructs continuity; no coherent strip map is assumed. -/
theorem projectedMap_continuousOn :
    ContinuousOn (D.projectedMap K) (K.footprint \ K.projectedCutSet retain) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let S := K.footprint \ K.projectedCutSet retain
  let piece : Face → Set S := fun f => {x | x.val ∈ (K.projectedTriangle f).carrier}
  have cover : ⋃ f, piece f = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨f, member⟩ := Set.mem_iUnion.mp
      (K.footprint_eq_union_projectedTriangles.subset x.property.1)
    exact Set.mem_iUnion.mpr ⟨f, member⟩
  have closed : ∀ f, IsClosed (piece f) :=
    fun f => (K.projectedTriangle f).compact_carrier.isClosed.preimage continuous_subtype_val
  apply (locallyFinite_of_finite piece).continuous cover closed
  intro f
  have continuous : Continuous (fun x : S => D.projectedPlacement K f x.val) :=
    (D.projectedPlacement K f).continuous_of_finiteDimensional.comp continuous_subtype_val
  apply continuous.continuousOn.congr
  intro x member
  exact D.projectedMap_eq K member x.property.2

end FacewiseDevelopment
end Unfoldings
