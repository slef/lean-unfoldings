module

public import Unfoldings.Metric.Excision

/-! Keep a selected subfamily of original closed seams without changing its domains. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing.ClosedSeams

variable {I : Type*} {E : I → Type*} [∀ i, MetricSpace (E i)]
  (S : ClosedSeams E) (keep : S.Seam → Prop)

/-- Keep exactly the selected original seams with their literal domains and maps. -/
def restrict : ClosedSeams E where
  Seam := {s : S.Seam // keep s}
  Domain s := S.Domain s.val
  left s := S.left s.val
  right s := S.right s.val
  toLeft s := S.toLeft s.val
  toRight s := S.toRight s.val
  left_isometry s := S.left_isometry s.val
  right_isometry s := S.right_isometry s.val
  left_closed s := S.left_closed s.val
  right_closed s := S.right_closed s.val

/-- Restoring discarded seams preserves every retained oriented identification. -/
theorem restrict_relation_included (a b : Total E)
    (joined : (S.restrict keep).relation a b) : S.relation a b := by
  obtain ⟨s, x, first, last⟩ := joined
  exact ⟨s.val, x, first, last⟩

/-- A selected original seam remains literally present at every original domain point. -/
theorem restrict_relation_of_mem (s : S.Seam) (member : keep s) (x : S.Domain s) :
    (S.restrict keep).relation ⟨S.left s, S.toLeft s x⟩ ⟨S.right s, S.toRight s x⟩ :=
  ⟨⟨s, member⟩, x, rfl, rfl⟩

/-- Keeping every seam incident to the chosen class preserves a whole small intrinsic ball.
No assumption is made about the geometry or connectivity of the discarded seams. -/
theorem exists_forgetChart_restrict (a : Total E)
    (finite : ∀ i, (classIn E S.relation a i).Finite)
    (kept : ∀ s, S.Incident a s → keep s) :
    Nonempty (ForgetChart E (S.restrict_relation_included keep) a) :=
  S.exists_forgetChart a finite (S.restrict keep).relation (S.restrict_relation_included keep)
    (fun s incident x => S.restrict_relation_of_mem keep s (kept s incident) x)

end Unfoldings.MetricGluing.ClosedSeams
