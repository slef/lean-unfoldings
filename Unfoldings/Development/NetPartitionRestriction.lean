module

public import Unfoldings.Development.NetPartition

/-! Flatten a whole-face restriction of a whole-face restriction, preserving the net. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (U : Set Face) (V : Set U)

local notation "Flat" => C.restrictFaces (Subtype.val '' V)
local notation "Nested" => TriangleComplex.restrictFaces (TriangleComplex.restrictFaces C U) V

open Classical in
local instance : Fintype ↑(Subtype.val '' V) := Subtype.fintype _

private def nestedFace (f : Subtype.val '' V) : V :=
  ⟨⟨f.val, by obtain ⟨g, _, h⟩ := f.property; exact h ▸ g.property⟩, by
    obtain ⟨g, hg, h⟩ := f.property
    exact (Subtype.ext h : g = ⟨f.val, _⟩) ▸ hg⟩

private def flatFace (f : V) : Subtype.val '' V :=
  ⟨f.val.val, f.val, f.property, rfl⟩

open Classical in
private def nestedSeam (s : (Flat).Seam) : (Nested).Seam :=
  ⟨⟨s.val, (nestedFace U V ((Flat).left s).face).val.property,
    (nestedFace U V ((Flat).right s).face).val.property⟩,
    (nestedFace U V ((Flat).left s).face).property, (nestedFace U V ((Flat).right s).face).property⟩

open Classical in
private def flatSeam (s : (Nested).Seam) : (Flat).Seam :=
  ⟨s.val.val, (flatFace U V ((Nested).left s).face).property,
    (flatFace U V ((Nested).right s).face).property⟩

open Classical in
private def flatRealizationIsometry (retain : Set (Nested).Seam) :
    (Flat).Realization (nestedSeam C U V ⁻¹' retain) ≃ᵢ (Nested).Realization retain := by
  let toNested := nestedFace U V
  let toFlat := flatFace U V
  let sn := nestedSeam C U V
  let sf := flatSeam C U V
  let keep := sn ⁻¹' retain
  have sn_sf (s : (Nested).Seam) : sn (sf s) = s :=
    Subtype.ext (Subtype.ext rfl)
  have sn_keep (s : (Flat).Seam) (kept : s ∈ keep) : sn s ∈ retain := kept
  have sf_keep (s : (Nested).Seam) (kept : s ∈ retain) : sf s ∈ keep := by
    change sn (sf s) ∈ retain
    rwa [sn_sf]
  let forward : (Flat).Realization keep → (Nested).Realization retain :=
    MetricGluing.lift (Flat).Cell ((Flat).glue keep)
      (fun f x => (Nested).faceMap retain (toNested f) x)
      (fun f => (Nested).faceMap_lipschitz retain (toNested f))
      (by
        rintro a b ⟨s, kept, x, rfl, rfl⟩
        exact (Nested).seam_identified retain (sn s) (sn_keep s kept) x)
  let reverse : (Nested).Realization retain → (Flat).Realization keep :=
    MetricGluing.lift (Nested).Cell ((Nested).glue retain)
      (fun f x => (Flat).faceMap keep (toFlat f) x)
      (fun f => (Flat).faceMap_lipschitz keep (toFlat f))
      (by
        rintro a b ⟨s, kept, x, rfl, rfl⟩
        exact (Flat).seam_identified keep (sf s) (sf_keep s kept) x)
  have left : Function.LeftInverse reverse forward := by
    intro x
    obtain ⟨⟨f, y⟩, rfl⟩ := MetricGluing.point_surjective (Flat).Cell ((Flat).glue keep) x
    rfl
  have right : Function.RightInverse reverse forward := by
    intro x
    obtain ⟨⟨f, y⟩, rfl⟩ := MetricGluing.point_surjective (Nested).Cell ((Nested).glue retain) x
    rfl
  have iso : Isometry forward := by
    intro x y
    have f_lip : LipschitzWith 1 forward := MetricGluing.lift_lipschitz _ _ _ _ _
    have r_lip : LipschitzWith 1 reverse := MetricGluing.lift_lipschitz _ _ _ _ _
    have first := f_lip.edist_le_mul x y
    have last := r_lip.edist_le_mul (forward x) (forward y)
    rw [left, left] at last
    simp only [ENNReal.coe_one, one_mul] at first last
    exact le_antisymm first last
  exact ⟨⟨forward, reverse, left, right⟩, iso⟩

open Classical in
/-- Flattening whole-face restrictions preserves the uncut intrinsic realization. -/
theorem nonempty_restrictFacesImageHomeomorph :
    Nonempty ((C.restrictFaces (Subtype.val '' V)).Realization Set.univ ≃ₜ
      ((C.restrictFaces U).restrictFaces V).Realization Set.univ) :=
  ⟨(flatRealizationIsometry C U V Set.univ).toHomeomorph⟩

open Classical in
/-- Flattening the two nested face subtypes preserves all literal original seam
names, the cut disk and the nonoverlap of the placements. -/
theorem hasOriginalEdgeNet_of_restrictFaces
    (net : (C.restrictFaces U).HasOriginalEdgeNet V) :
    C.HasOriginalEdgeNet (Subtype.val '' V) := by
  obtain ⟨retain, ⟨disk⟩, D, disjoint⟩ := net
  let toNested := nestedFace U V
  let toFlat := flatFace U V
  let sn := nestedSeam C U V
  let keep := sn ⁻¹' retain
  let I := flatRealizationIsometry C U V retain
  let development : FacewiseDevelopment (Flat) keep :=
    { place := fun f => D.place (toNested f)
      joined := fun s kept x => D.joined (sn s) kept x
      opposite := fun s kept => D.opposite (sn s) kept }
  refine ⟨keep, ⟨I.toHomeomorph.trans disk⟩, development, ?_⟩
  intro f g different
  exact disjoint (toNested f) (toNested g) (fun h => different (congrArg toFlat h))

end Unfoldings.TriangleComplex
