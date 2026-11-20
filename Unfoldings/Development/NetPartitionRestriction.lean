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

private def nestedFace (f : Subtype.val '' V) : V :=
  ⟨⟨f.val, by obtain ⟨g, _, h⟩ := f.property; exact h ▸ g.property⟩, by
    obtain ⟨g, hg, h⟩ := f.property
    exact (Subtype.ext h : g = ⟨f.val, _⟩) ▸ hg⟩

private def flatFace (f : V) : Subtype.val '' V :=
  ⟨f.val.val, f.val, f.property, rfl⟩

open Classical in
/-- Flattening the two nested face subtypes preserves all literal original seam
names, the cut disk and the nonoverlap of the placements. -/
theorem hasOriginalEdgeNet_of_restrictFaces
    (net : (C.restrictFaces U).HasOriginalEdgeNet V) :
    C.HasOriginalEdgeNet (Subtype.val '' V) := by
  let : Fintype ↑(Subtype.val '' V) := Subtype.fintype _
  obtain ⟨retain, ⟨disk⟩, D, disjoint⟩ := net
  let toNested := nestedFace U V
  let toFlat := flatFace U V
  let sn (s : (Flat).Seam) : (Nested).Seam :=
    ⟨⟨s.val, (toNested ((Flat).left s).face).val.property,
      (toNested ((Flat).right s).face).val.property⟩,
      (toNested ((Flat).left s).face).property, (toNested ((Flat).right s).face).property⟩
  let sf (s : (Nested).Seam) : (Flat).Seam :=
    ⟨s.val.val, (toFlat ((Nested).left s).face).property,
      (toFlat ((Nested).right s).face).property⟩
  let keep : Set (Flat).Seam := sn ⁻¹' retain
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
  let I : (Flat).Realization keep ≃ᵢ (Nested).Realization retain :=
    ⟨⟨forward, reverse, left, right⟩, iso⟩
  let development : FacewiseDevelopment (Flat) keep :=
    { place := fun f => D.place (toNested f)
      joined := fun s kept x => D.joined (sn s) (sn_keep s kept) x
      opposite := fun s kept => D.opposite (sn s) (sn_keep s kept) }
  refine ⟨keep, ⟨I.toHomeomorph.trans disk⟩, development, ?_⟩
  intro f g different
  exact disjoint (toNested f) (toNested g) (fun h => different (congrArg toFlat h))

end Unfoldings.TriangleComplex
