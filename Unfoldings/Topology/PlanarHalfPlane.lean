module

public import Unfoldings.Topology.PlanarOpenMapping
public import Unfoldings.Topology.Quadrant

/-! Planar openness in product coordinates and the boundary obstruction for a half-plane. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

def pairHomeomorph : (ℝ × ℝ) ≃ₜ Plane :=
  Complex.equivRealProdCLM.symm.toHomeomorph.trans complexIsometry.toHomeomorph

theorem isOpen_range_pair_of_openEmbedding {A : Type*} [TopologicalSpace A]
    (i : A → Plane) (embedding : Topology.IsOpenEmbedding i)
    (f : C(A, ℝ × ℝ)) (injective : Function.Injective f) : IsOpen (Set.range f) := by
  let g : C(A, Plane) := ⟨pairHomeomorph ∘ f, pairHomeomorph.continuous.comp f.continuous⟩
  have open_range := isOpen_range_of_openEmbedding i embedding g
    (pairHomeomorph.injective.comp injective)
  have equality : Set.range f = pairHomeomorph ⁻¹' Set.range g := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, equal⟩
      exact ⟨x, pairHomeomorph.injective equal⟩
  rw [equality]
  exact open_range.preimage pairHomeomorph.continuous

theorem positive_snd_of_open_subset_halfPlane {S : Set (ℝ × ℝ)} (open_S : IsOpen S)
    (contained : S ⊆ closedHalfPlane) {p : ℝ × ℝ} (inside : p ∈ S) : 0 < p.2 := by
  have open_image : IsOpen (Prod.snd '' S) := isOpenMap_snd _ open_S
  have included : Prod.snd '' S ⊆ Set.Ici (0 : ℝ) := by
    rintro _ ⟨q, hq, rfl⟩
    exact contained hq
  have image_mem : p.2 ∈ Prod.snd '' S := ⟨p, inside, rfl⟩
  have interior := interior_mono included (open_image.interior_eq.symm ▸ image_mem)
  rwa [interior_Ici] at interior

theorem positive_snd_of_planar_injection {A : Type*} [TopologicalSpace A]
    (i : A → Plane) (embedding : Topology.IsOpenEmbedding i)
    (f : C(A, closedHalfPlane)) (injective : Function.Injective f) (a : A) :
    0 < (f a).val.2 := by
  let g : C(A, ℝ × ℝ) := ⟨Subtype.val ∘ f, continuous_subtype_val.comp f.continuous⟩
  have inj : Function.Injective g := fun _ _ equal => injective (Subtype.ext equal)
  have open_range := isOpen_range_pair_of_openEmbedding i embedding g inj
  exact positive_snd_of_open_subset_halfPlane open_range
    (by rintro _ ⟨x, rfl⟩; exact (f x).property) ⟨a, rfl⟩

def halfPlaneInterior : Set closedHalfPlane := {p | 0 < p.val.2}

theorem isOpen_halfPlaneInterior : IsOpen halfPlaneInterior :=
  isOpen_lt continuous_const continuous_subtype_val.snd

theorem halfPlaneInterior_openEmbedding :
    Topology.IsOpenEmbedding (fun p : halfPlaneInterior => pairHomeomorph p.val.val) := by
  have embedding : Topology.IsEmbedding (fun p : halfPlaneInterior => p.val.val) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have image : Set.range (fun p : halfPlaneInterior => p.val.val) =
      {p : ℝ × ℝ | 0 < p.2} := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact q.property
    · intro positive
      change 0 < p.2 at positive
      exact ⟨⟨⟨p, by exact positive.le⟩, positive⟩, rfl⟩
  have open_range : IsOpen (Set.range (fun p : halfPlaneInterior => p.val.val)) := by
    rw [image]
    exact isOpen_lt continuous_const continuous_snd
  exact pairHomeomorph.isOpenEmbedding.comp ⟨embedding, open_range⟩

end Unfoldings.PlanarTopology
