module

public import Unfoldings.Source.ShortestPath

/-! Actual constant-speed shortest-path prefixes, including zero and full time. -/

@[expose] public section

namespace Unfoldings.SourcePath

variable {X : Type*} [MetricSpace X] {source : X}

def initial (p : SourcePath source) (t : unitInterval) : SourcePath source where
  target := p.path t
  path :=
    { toFun := fun u => p.path (Path.intervalParam 0 t u)
      continuous_toFun := p.path.continuous.comp (Path.continuous_intervalParam 0 t)
      source' := by simp
      target' := by simp }
  geodesic := by
    intro u v
    change edist (p.path (Path.intervalParam 0 t u)) (p.path (Path.intervalParam 0 t v)) =
      edist source (p.path t) * edist u v
    have shortest := p.geodesic.subpath 0 t u v
    simpa only [Path.subpath_apply, Path.source] using shortest

@[simp] theorem initial_apply (p : SourcePath source) (t u : unitInterval) :
    (p.initial t).path u = p.path (Path.intervalParam 0 t u) := rfl

@[simp] theorem initial_target (p : SourcePath source) (t : unitInterval) :
    (p.initial t).target = p.path t := rfl

@[simp] theorem initial_one (p : SourcePath source) : p.initial 1 = p := by
  apply SourcePath.ext
  intro t
  rw [initial_apply]
  congr 1
  apply Subtype.ext
  change AffineMap.lineMap (0 : ℝ) 1 (t : ℝ) = (t : ℝ)
  simp [AffineMap.lineMap_apply_ring]

@[simp] theorem initial_zero (p : SourcePath source) :
    p.initial 0 = SourcePath.constant source := by
  apply SourcePath.ext
  intro t
  change p.path (Path.intervalParam 0 0 t) = source
  have zero : Path.intervalParam 0 0 t = 0 := by
    apply Subtype.ext
    simp [Path.intervalParam]
  rw [zero, Path.source]

end Unfoldings.SourcePath
