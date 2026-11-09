module

public import Unfoldings.Path.Length
public import Unfoldings.Metric.FiniteComponent

/-! Rectifiable paths lift to finite-distance components without changing length. -/

@[expose] public section

open scoped ENNReal

namespace Path

variable {X : Type*} [EMetricSpace X] {a b c : X}

theorem edist_apply_source_ne_top (p : Path a b) (finite : p.eLength ≠ ⊤) (t : unitInterval) :
    edist (p t) a ≠ ⊤ :=
  ne_top_of_le_ne_top finite (by simpa only [Path.source] using p.edist_apply_le_eLength t 0)

theorem finiteComponent_target (p : Path a b) (start : edist a c ≠ ⊤) (finite : p.eLength ≠ ⊤) :
    edist b c ≠ ⊤ := by
  apply Unfoldings.finite_edist_trans (y := a) ?_ start
  simpa only [Path.target] using p.edist_apply_source_ne_top finite 1

/-- Restrict a rectifiable path to the ordinary metric component containing its source. -/
noncomputable def toFiniteComponent (p : Path a b) (start : edist a c ≠ ⊤)
    (finite : p.eLength ≠ ⊤) :
    Path (⟨a, start⟩ : Unfoldings.FiniteComponent c)
      ⟨b, p.finiteComponent_target start finite⟩ where
  toFun := fun t => ⟨p t, Unfoldings.finite_edist_trans
    (p.edist_apply_source_ne_top finite t) start⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

@[simp] theorem toFiniteComponent_apply (p : Path a b) (start : edist a c ≠ ⊤)
    (finite : p.eLength ≠ ⊤) (t : unitInterval) :
    (p.toFiniteComponent start finite t).val = p t := rfl

@[simp] theorem toFiniteComponent_map_val (p : Path a b) (start : edist a c ≠ ⊤)
    (finite : p.eLength ≠ ⊤) :
    (p.toFiniteComponent start finite).map continuous_subtype_val = p := by
  ext t
  rfl

@[simp] theorem eLength_toFiniteComponent (p : Path a b) (start : edist a c ≠ ⊤)
    (finite : p.eLength ≠ ⊤) : (p.toFiniteComponent start finite).eLength = p.eLength := by
  have same := (p.toFiniteComponent start finite).eLength_map_isometry
    (Unfoldings.FiniteComponent.val_isometry c)
  rw [toFiniteComponent_map_val] at same
  exact same.symm

end Path
