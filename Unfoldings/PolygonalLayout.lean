module

public import Unfoldings.Complex.Folding
public import Unfoldings.Geometry.AffineArrangement

/-!
# Polygonal layouts with rigid maps to original triangles

Pieces are indexed separately even when their developed polygons overlap.
Each piece has its own rigid folding map into an original triangle. There is
no global inverse map from the planar footprint in this general interface.
Nonoverlap is a separate predicate and permits boundary contacts.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

universe u v w

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (Piece : Type w)

structure FacePolygonalLayout where
  finite_pieces : Finite Piece
  region : Piece → Set Plane
  halfplanes : Piece → Set (Plane →ᵃ[ℝ] ℝ)
  finite_halfplanes : ∀ i, (halfplanes i).Finite
  region_eq : ∀ i, region i = {x | ∀ l ∈ halfplanes i, 0 ≤ l x}
  compact_region : ∀ i, IsCompact (region i)
  interior_nonempty : ∀ i, (interior (region i)).Nonempty
  face : Piece → Face
  foldPlacement : Piece → Plane ≃ᵃⁱ[ℝ] Plane
  in_face : ∀ i, ∀ x ∈ region i, foldPlacement i x ∈ (C.triangle (face i)).carrier

namespace FacePolygonalLayout

variable {C Piece} (D : FacePolygonalLayout C Piece)

def Total := (i : Piece) × D.region i

def develop (x : D.Total) : Plane := x.2.val

def fold (retain : Set C.Seam) (i : Piece) (x : D.region i) : C.Realization retain :=
  C.faceMap retain (D.face i) ⟨D.foldPlacement i x.val, D.in_face i x.val x.property⟩

def footprint : Set Plane := ⋃ i, D.region i

def Nonoverlapping : Prop :=
  Pairwise (fun i j => Disjoint (interior (D.region i)) (interior (D.region j)))

theorem convex_region (i : Piece) : Convex ℝ (D.region i) := by
  rw [D.region_eq]
  have equal : {x | ∀ l ∈ D.halfplanes i, 0 ≤ l x} =
      ⋂ l ∈ D.halfplanes i, l ⁻¹' Set.Ici 0 := by ext; simp
  rw [equal]
  exact convex_iInter₂ (fun l _ => (convex_Ici (0 : ℝ)).affine_preimage l)

theorem mem_footprint (i : Piece) (x : D.region i) : x.val ∈ D.footprint :=
  Set.mem_iUnion.mpr ⟨i, x.property⟩

theorem range_develop : Set.range D.develop = D.footprint := by
  ext x
  constructor
  · rintro ⟨⟨i, y⟩, rfl⟩
    exact D.mem_footprint i y
  · intro member
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
    exact ⟨⟨i, ⟨x, hi⟩⟩, rfl⟩

theorem fold_isometry (F : SpatialFolding C) (retain : Set C.Seam) (i : Piece) :
    Isometry (D.fold retain i) := by
  let into (x : D.region i) : C.Cell (D.face i) :=
    ⟨D.foldPlacement i x.val, D.in_face i x.val x.property⟩
  have isometry : Isometry into := by
    intro x y
    exact (D.foldPlacement i).isometry x.val y.val
  exact (F.faceMap_isometry retain (D.face i)).comp isometry

def duplicate : FacePolygonalLayout C (Piece × Bool) where
  finite_pieces := by
    let := D.finite_pieces
    infer_instance
  region := fun i => D.region i.1
  halfplanes := fun i => D.halfplanes i.1
  finite_halfplanes := fun i => D.finite_halfplanes i.1
  region_eq := fun i => D.region_eq i.1
  compact_region := fun i => D.compact_region i.1
  interior_nonempty := fun i => D.interior_nonempty i.1
  face := fun i => D.face i.1
  foldPlacement := fun i => D.foldPlacement i.1
  in_face := fun i => D.in_face i.1

theorem duplicate_overlaps [Nonempty Piece] : ¬ D.duplicate.Nonoverlapping := by
  intro nonoverlap
  let i : Piece := Classical.choice inferInstance
  obtain ⟨x, inside⟩ := D.interior_nonempty i
  have different : (i, false) ≠ (i, true) := by simp
  exact Set.disjoint_left.mp (nonoverlap different) inside inside

end FacePolygonalLayout

end Unfoldings
