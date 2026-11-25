module

public import Unfoldings.Basic
public import Unfoldings.Topology.SphereChart
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Connected.Clopen

/-! A closed unit-sphere patch with only finitely many possible boundary points covers the sphere. -/

@[expose] public section

noncomputable section

namespace Unfoldings

local notation "Sphere" => Subtype (fun p : Space => p ∈ Metric.sphere (0 : Space) 1)

/-- Deleting finitely many vertices of the two-dimensional unit sphere
leaves a path-connected set. -/
theorem unitSphere_isPathConnected_compl_finite {excluded : Set Sphere}
    (finite : excluded.Finite) (nonempty : excluded.Nonempty) :
    IsPathConnected excludedᶜ := by
  obtain ⟨pole, missed⟩ := nonempty
  let : Fact (Module.finrank ℝ Space = 2 + 1) := ⟨by norm_num [Space]⟩
  let h := spherePunctureHomeomorph 2 pole
  let source := ({pole} : Set Sphere)ᶜ
  let blocked : Set source := Subtype.val ⁻¹' excluded
  have finite_blocked : blocked.Finite := finite.preimage Subtype.val_injective.injOn
  let image := h '' blocked
  have dimension : 1 < Module.rank ℝ Plane := by
    rw [← Module.finrank_eq_rank]
    norm_num [Plane]
  have connected := (finite_blocked.image h).countable.isPathConnected_compl_of_one_lt_rank dimension
  have cover : (Subtype.val ∘ h.symm) '' imageᶜ = excludedᶜ := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩ hp
      apply hq
      exact ⟨h.symm q, hp, h.apply_symm_apply q⟩
    · intro hp
      have ne : p ≠ pole := fun equal => hp (equal.symm ▸ missed)
      let x : source := ⟨p, ne⟩
      refine ⟨h x, ?_, congrArg Subtype.val (h.symm_apply_apply x)⟩
      rintro ⟨y, hy, same⟩
      have cast : y.val = p := congrArg Subtype.val (h.injective same)
      exact hp (cast ▸ (show y.val ∈ excluded from hy))
  rw [← cover]
  exact connected.image (continuous_subtype_val.comp h.symm.continuous)

/-- Once every nonvertex point of a closed spherical patch has a
neighborhood in the patch, any nonvertex point certifies full coverage. -/
theorem unitSphere_eq_univ_of_finite_boundary {patch vertices : Set Sphere}
    (closed : IsClosed patch) (finite : vertices.Finite) (nonempty : vertices.Nonempty)
    (included : vertices ⊆ patch) (interior_at : patch \ vertices ⊆ interior patch)
    (has_face : (patch \ vertices).Nonempty) : patch = Set.univ := by
  let : PreconnectedSpace (verticesᶜ : Set Sphere) :=
    Subtype.preconnectedSpace (unitSphere_isPathConnected_compl_finite finite nonempty).isConnected.isPreconnected
  let U : Set (verticesᶜ : Set Sphere) := Subtype.val ⁻¹' patch
  have same : U = Subtype.val ⁻¹' interior patch := by
    ext x
    change x.val ∈ patch ↔ x.val ∈ interior patch
    exact ⟨fun inside => interior_at ⟨inside, x.property⟩, fun hx => @interior_subset Sphere _ patch x.val hx⟩
  have clopen : IsClopen U :=
    ⟨closed.preimage continuous_subtype_val, by rw [same]; exact isOpen_interior.preimage continuous_subtype_val⟩
  obtain ⟨x, hx, outside⟩ := has_face
  have all : U = Set.univ := clopen.eq_univ ⟨⟨x, outside⟩, hx⟩
  apply Set.eq_univ_of_forall
  intro y
  by_cases member : y ∈ vertices
  · exact included member
  · have here : (⟨y, member⟩ : (verticesᶜ : Set Sphere)) ∈ U := by rw [all]; trivial
    exact here

end Unfoldings
