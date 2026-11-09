module

public import Unfoldings.Path.Geodesic

/-!
# Restricting paths to their actual range

Codomain restriction retains the underlying path, its length and its
constant-speed geodesic property. Isometric maps preserve geodesics as well.
-/

@[expose] public section

namespace Path

variable {X : Type*} [TopologicalSpace X] {a b : X}

def codRestrict (p : Path a b) (s : Set X) (ha : a ∈ s) (hb : b ∈ s)
    (inside : ∀ t, p t ∈ s) : Path (⟨a, ha⟩ : s) ⟨b, hb⟩ where
  toFun t := ⟨p t, inside t⟩
  continuous_toFun := p.continuous.subtype_mk inside
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

@[simp] theorem codRestrict_apply (p : Path a b) (s : Set X) (ha : a ∈ s) (hb : b ∈ s)
    (inside : ∀ t, p t ∈ s) (t : unitInterval) :
    (p.codRestrict s ha hb inside t).val = p t := rfl

end Path

namespace Path

variable {X : Type*} [PseudoEMetricSpace X] {a b : X} {p : Path a b}

theorem IsGeodesic.codRestrict (geodesic : p.IsGeodesic) (s : Set X)
    (ha : a ∈ s) (hb : b ∈ s) (inside : ∀ t, p t ∈ s) :
    (p.codRestrict s ha hb inside).IsGeodesic := fun u v => geodesic u v

theorem eLength_codRestrict (p : Path a b) (s : Set X) (ha : a ∈ s) (hb : b ∈ s)
    (inside : ∀ t, p t ∈ s) : (p.codRestrict s ha hb inside).eLength = p.eLength := by
  let q := p.codRestrict s ha hb inside
  have same : q.map continuous_subtype_val = p := by ext t; rfl
  have length := q.eLength_map_isometry (isometry_subtype_coe (s := s))
  rw [same] at length
  exact length.symm

variable {Y : Type*} [PseudoEMetricSpace Y]

theorem IsGeodesic.map_isometry (geodesic : p.IsGeodesic) (f : X → Y) (isometry : Isometry f) :
    (p.map isometry.continuous).IsGeodesic := by
  intro s t
  change edist (f (p s)) (f (p t)) = edist (f a) (f b) * edist s t
  rw [isometry.edist_eq, isometry.edist_eq]
  exact geodesic s t

end Path
