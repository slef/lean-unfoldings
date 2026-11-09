module

public import Unfoldings.Path.MetricGeodesic

/-! All actual normalized shortest paths from a named source, retaining route ties. -/

@[expose] public section

namespace Unfoldings

variable {X : Type*} [MetricSpace X]

/-- Different shortest paths to the same target remain different elements. -/
structure SourcePath (source : X) where
  target : X
  path : Path source target
  geodesic : path.IsGeodesic

namespace SourcePath

variable {source : X}

@[ext] theorem ext {p q : SourcePath source} (equal : ∀ t, p.path t = q.path t) : p = q := by
  obtain ⟨a, p, geodesic⟩ := p
  obtain ⟨b, q, other⟩ := q
  have endpoints : a = b := by simpa only [Path.target] using equal 1
  subst b
  have paths : p = q := by ext t; exact equal t
  subst q
  rfl

theorem eq_source_of_target_eq {p : SourcePath source} (equal : p.target = source)
    (t : unitInterval) : p.path t = source := by
  apply dist_eq_zero.mp
  rw [dist_comm, p.geodesic.dist_source, equal, dist_self, zero_mul]

def constant (source : X) : SourcePath source :=
  ⟨source, Path.refl source, fun _ _ => by simp⟩

end SourcePath
end Unfoldings
